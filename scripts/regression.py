#!/usr/bin/env python3

import argparse
import difflib
import multiprocessing
import os
import platform
import pprint
import psutil
import re
import shutil
import subprocess
import sys
import time
import traceback
from collections import OrderedDict
from contextlib import redirect_stdout, redirect_stderr
from datetime import datetime, timedelta
from enum import Enum, unique
from pathlib import Path
from threading import Lock

import blacklisted

_this_filepath = os.path.realpath(__file__)
_default_workspace_dirpath = os.path.dirname(os.path.dirname(_this_filepath))

# Except for the workspace dirpath all paths are expected to be relative
# either to the workspace directory or the build directory
_default_test_dirpaths = [ 'tests', os.path.join('third_party', 'tests') ]
_default_build_dirpath = 'build'
# _default_build_dirpath = os.path.join('out', 'build', 'Debug')
_default_output_dirpath = 'regression'
_default_surelog_filename = 'surelog.exe' if platform.system() == 'Windows' else 'surelog'
_default_uhdm_dump_filename = 'uhdm-dump.exe' if platform.system() == 'Windows' else 'uhdm-dump'
_default_roundtrip_filename = 'roundtrip.exe' if platform.system() == 'Windows' else 'roundtrip'
_default_surelog_filepath = os.path.join('bin', _default_surelog_filename)
_default_uhdm_dump_filepath = os.path.join('third_party', 'UHDM', 'bin', _default_uhdm_dump_filename)
_default_roundtrip_filepath = os.path.join('bin', _default_roundtrip_filename)

_re_status_1 = re.compile(r'^\s*\[\s*(?P<status>\w+)\]\s*:\s*(?P<count>\d+)$')
_re_status_2 = re.compile(r'^\s*\|\s*(?P<status>\w+)\s*\|\s*(?P<count1>\d+|\s+)\s*\|\s*(?P<count2>\d+|\s+)\s*\|\s*$')
_re_status_3 = re.compile(r'^\[roundtrip\]: (?P<original>.+)\s*\|\s*(?P<generated>.+)\s*\|\s*(?P<diffcount>\d+)\s*\|\s*(?P<linecount>\d+)\s*\|\s*$')


_log_mutex = Lock()
def log(text, end='\n'):
  _log_mutex.acquire()
  try:
    print(text, end=end, flush=True)
  finally:
    _log_mutex.release()

@unique
class Status(Enum):
  PASS = 0
  DIFF = -1
  FAIL = -2
  FAILDUMP = -3
  SEGFLT = -4
  NOGOLD = -5
  TOOLFAIL = -6

  def __str__(self):
    return str(self.name)


def _transform_path(path):
  if 'MSYSTEM' not in os.environ:
    return path

  path = path.replace('/', '\\').replace('\\\\', '\\').replace('\\', '\\\\')
  result = subprocess.run(['cygpath', '-u', path], capture_output=True, text=True)
  result.check_returncode()
  return result.stdout.strip()


def _find_files(dirpath, pattern):
  relpaths = []
  for filepath in Path(dirpath).rglob(pattern):
    relpaths.append(os.path.relpath(filepath, dirpath))

  if 'MSYSTEM' in os.environ:
    relpaths = [relpath.replace('\\', '/') for relpath in relpaths]

  return sorted(relpaths)


def _mkdir(dirpath, retries=10):
  count = 0
  while count < retries:
    os.makedirs(dirpath, exist_ok=True)

    if os.path.exists(dirpath):
      return True

    count += 1
    time.sleep(0.1)

  return os.path.exists(dirpath)


def _rmdir(dirpath, retries=10):
  count = 0
  while count < retries:
    shutil.rmtree(dirpath, ignore_errors=True)

    if not os.path.exists(dirpath):
      return True

    count += 1
    time.sleep(0.1)

  shutil.rmtree(dirpath)
  return not os.path.exists(dirpath)


def _remove_dirs(dirpath, patterns):
  for pattern in patterns:
    for path in Path(dirpath).rglob(pattern):
      if os.isdir(path):
        shutil.rmtree(path)


def _scan(dirpaths, filters):
  def _is_filtered(name):
    for filter in filters:
      if isinstance(filter, str):
        if filter.lower() == name.lower():
          return True
      else:
        if filter.search(name):  # Note: match() reports success only if the match is at index 0
          return True

    return False

  all_tests = {}
  filtered_tests = set()
  blacklisted_tests = set()
  for dirpath in dirpaths:
    for sub_dirpath, sub_dirnames, filenames in os.walk(dirpath):
      for filename in filenames:
        if filename.endswith('.sl'):
          name = filename[:-3]
          filepath = os.path.join(sub_dirpath, filename)

          all_tests[name] = filepath
          if blacklisted.is_blacklisted(name):
            blacklisted_tests.add(name)
          elif not filters or _is_filtered(name):
            filtered_tests.add(name)

  return [
    OrderedDict([ (name, all_tests[name]) for name in sorted(all_tests.keys(), key=lambda t: t.lower()) ]),
    OrderedDict([ (name, all_tests[name]) for name in sorted(filtered_tests, key=lambda t: t.lower()) ]),
    OrderedDict([ (name, all_tests[name]) for name in sorted(blacklisted_tests, key=lambda t: t.lower()) ])
  ]


def _snapshot_directory_state(dirpath):
  snapshot = set()
  for sub_dirpath, sub_dirnames, filenames in os.walk(dirpath):
    snapshot.add(sub_dirpath)
    snapshot.update([os.path.join(sub_dirpath, filename) for filename in filenames])

  return snapshot


def _restore_directory_state(dirpath, golden_snapshot, output_dirpath, current_snapshot):
  dirt = set(current_snapshot).difference(set(golden_snapshot))
  # Sort based on the length of the string and then chronologically
  dirt = sorted(dirt, key=lambda item: (len(item), item))

  for path in dirt:
    if os.path.isdir(path) or os.path.isfile(path):
      src_rel_path = os.path.relpath(path, dirpath)
      dst_abs_path = os.path.join(output_dirpath, src_rel_path)
      try:
        _mkdir(os.path.dirname(dst_abs_path))
        shutil.move(path, dst_abs_path)
      except:
        print(f'Failed to move {path} to {dst_abs_path}')
        traceback.print_exc()


def _normalize_log(content, path_mappings):
  content = re.sub(r'\d+\.\d{3}s', 't.ttts', content)
  content = re.sub(r'\d+\.\d{6}s', 't.tttttts', content)
  for path, mapping in path_mappings.items():
    pattern = re.sub(r'(\\|\/)+', r'(\\\\|\/)+', path)
    content = re.sub(pattern, mapping, content)
  return content


def _get_log_statistics(filepath):
  # For the time being don't allow the regression to fail because of
  # differences in roundtrip results. This is still work in progress!!
  statistics = { 'ROUNDTRIP_A': 0, 'ROUNDTRIP_B': 0 }
  if not os.path.isfile(filepath):
    return statistics

  negatives = {}
  notes = 0
  uhdm_dump_started = False
  uhdm_line_count = 0
  with open(filepath, 'rt', encoding='cp850') as strm:
    for line in strm:
      line = line.strip()

      if line == '====== UHDM =======':
        uhdm_dump_started = True
        continue
      elif uhdm_dump_started and line == '===================':
        uhdm_dump_started = False
        continue

      m = _re_status_3.match(line)
      if m:
        statistics['ROUNDTRIP_A'] = statistics.get('ROUNDTRIP_A', 0) + int(m.group('diffcount').strip())
        statistics['ROUNDTRIP_B'] = statistics.get('ROUNDTRIP_B', 0) + int(m.group('linecount').strip())
      else:
        m = _re_status_2.match(line)
        if m:
          count1 = m.group('count1').strip()
          count2 = m.group('count2').strip()
          count1 = int(count1) if count1 else 0
          count2 = int(count2) if count2 else 0
          statistics[m.group('status')] = statistics.get(m.group('status'), 0) + count1 + count2
        else:
          m = _re_status_1.match(line)
          if m:
            statistics[m.group('status')] = int(m.group('count'))
          elif uhdm_dump_started and (line.startswith('|') or line.startswith('\\')):
            uhdm_line_count += 1

        if 'ERR:' in line and '/dev/null' in line:
          # On Windows, this is reported as an error but on Linux it isn't.
          # Don't count it as error on Windows as well so that numbers across platforms can match.
          negatives['ERROR'] = negatives.get('ERROR', 0) + 1

  statistics['NOTE'] = statistics.get('NOTE', 0) + uhdm_line_count

  for key, value in negatives.items():
    statistics[key] = max(statistics.get(key, 0) - value, 0)

  return statistics


def _run_surelog(
    name, filepath, dirpath, workspace_dirpath, surelog_filepath,
    surelog_log_filepath, uvm_reldirpath, mp, mt, tool, output_dirpath):
  start_dt = datetime.now()
  print(f'start-time: {start_dt}')

  tool_log_filepath = None
  tool_args_list = []
  if tool == 'valgrind':
    tool_log_filepath = os.path.join(output_dirpath, 'valgrind.log')
    tool_args_list = ['valgrind', '--tool=memcheck', f'--log-file={tool_log_filepath}']
  elif tool == 'ddd':
    tool_args_list = ['ddd']

  if tool_args_list:
    print('Tool args list:')
    pprint.pprint(tool_args_list)
    print('\n')

  cmdline = open(filepath, 'rt').read().strip()
  print(f'Loaded command line: {cmdline}')

  cmdline = cmdline.replace('\r', '')
  cmdline = cmdline.replace('\\', '')
  cmdline = cmdline.replace('\n', ' ')
  cmdline = cmdline.replace('"', '\\"')
  cmdline = cmdline.replace("'", "\\'")
  cmdline = re.sub('[.\\\/]+[\\\/]UVM', uvm_reldirpath.replace('\\', '\\\\'), cmdline)
  cmdline = cmdline.strip()

  status = Status.PASS
  surelog_timedelta = timedelta(seconds=0)
  max_cpu_time = 0
  max_vms_memory = 0
  max_rss_memory = 0
  if '.sh' in cmdline or '.bat' in cmdline:
    args = ['sh'] + [arg for arg in cmdline.split() if arg] + [_transform_path(surelog_filepath)]
  else:
    if '*/*.v' in cmdline:
      cmdline = cmdline.replace('*/*.v', ' '.join(_find_files(dirpath, '*.v')))
    if '*/*.sv' in cmdline:
      cmdline = cmdline.replace('*/*.sv', ' '.join(_find_files(dirpath, '*.sv')))
    if '-mt' in cmdline:
      cmdline = re.sub('-mt\s+(max|\d+)', '', cmdline)
    if mp > 0:
      cmdline = cmdline.replace('-nocache', '')

    parts = cmdline.split(' ')
    for i in range(0, len(parts)):
      if parts[i] and ('*' in parts[i] or '?' in parts[i]):
          if parts[i].endswith('.v') or parts[i].endswith('.sv') or parts[i].endswith('.pkg'):
            parts[i] = ' '.join(_find_files(dirpath, parts[i]))

    rel_output_dirpath = os.path.relpath(output_dirpath, dirpath)
    if 'MSYSTEM' in os.environ:
      rel_output_dirpath = rel_output_dirpath.replace('\\', '/')

    cmdline = ' '.join([part for part in parts if part] + [
      '-mt', str(mt),
      '-mp', '1' if '-lowmem' in cmdline else str(mp),
      '-o', rel_output_dirpath
    ])
    cmdline = ' '.join(['"' + arg + '"' if '"' in arg else arg for arg in cmdline.split() if arg])
    print(f'Processed command line: {cmdline}')

    args = tool_args_list + [surelog_filepath] + cmdline.split()

    # MSYS2 seems to be having some issues when working with quoted
    # argument on command line, specifically, when passing arguments
    # as list of strings. The only solution found to be working
    # reliably is to pass the arguments as a string rather than list
    # of strings.
    if '"' in cmdline and 'MSYSTEM' in os.environ:
      args = ' '.join(args)

  print('Launching surelog with arguments:')
  pprint.pprint(args)
  print('\n')

  with open(surelog_log_filepath, 'wt', encoding='cp850') as surelog_log_strm:
    surelog_start_dt = datetime.now()
    try:
      process = subprocess.Popen(
          args,
          stdout=surelog_log_strm,
          stderr=subprocess.STDOUT,
          cwd=dirpath)

      while psutil.pid_exists(process.pid) and process.poll() == None:
        cpu_time = 0
        rss_memory = 0
        vms_memory = 0
        try:
          pp = psutil.Process(process.pid)

          descendants = list(pp.children(recursive=True))
          descendants = [pp] + descendants

          for descendant in descendants:
            try:
              cpu_time += descendant.cpu_times().user

              mem_info = descendant.memory_info()
              rss_memory += mem_info.rss
              vms_memory += mem_info.vms
            except (psutil.NoSuchProcess, psutil.AccessDenied):
              # sometimes a subprocess descendant will have terminated between the time
              # we obtain a list of descendants, and the time we actually poll this
              # descendant's memory usage.
              pass

        except (psutil.NoSuchProcess, psutil.AccessDenied):
          pass

        max_cpu_time = max(max_cpu_time, cpu_time)
        max_vms_memory = max(max_vms_memory, vms_memory)
        max_rss_memory = max(max_rss_memory, rss_memory)

        time.sleep(0.5)

      returncode = process.poll()
      surelog_timedelta = datetime.now() - surelog_start_dt
      print(f'Surelog terminated with exit code: {returncode} in {str(surelog_timedelta)}')
    except:
      status = Status.FAIL
      surelog_timedelta = datetime.now() - surelog_start_dt
      print(f'Surelog threw an exception')
      traceback.print_exc()

    surelog_log_strm.flush()

  if status == Status.PASS and tool_log_filepath and os.path.isfile(tool_log_filepath):
    content = open(tool_log_filepath, 'rt').read()
    if 'ERROR SUMMARY: 0' not in content:
      status = Status.TOOLFAIL

  end_dt = datetime.now()
  delta = end_dt - start_dt
  print(f'end-time: {str(end_dt)} {str(delta)}')

  return {
    'STATUS': status,
    'CPU-TIME': max_cpu_time,
    'VTL-MEM': max_vms_memory,
    'PHY-MEM': max_rss_memory,
    'WALL-TIME': surelog_timedelta
  }


def _run_uhdm_dump(
    name, uhdm_dump_filepath, uhdm_src_filepath, uhdm_dump_log_filepath, output_dirpath):
  start_dt = datetime.now()
  print(f'start-time: {start_dt}')

  status = Status.PASS
  uhdm_args = [uhdm_dump_filepath, uhdm_src_filepath]

  print('Launching uhdm-dump with arguments:')
  pprint.pprint(uhdm_args)
  print('\n')

  with open(uhdm_dump_log_filepath, 'wt', encoding='cp850') as uhdm_dump_log_strm:
    try:
      result = subprocess.run(
          uhdm_args,
          stdout=uhdm_dump_log_strm,
          stderr=subprocess.STDOUT,
          check=False,
          cwd=os.path.dirname(uhdm_dump_filepath))
      print(f'uhdm-dump terminated with exit code: {result.returncode}')
    except:
      status = Status.FAILDUMP
      print(f'uhdm-dump threw an exception')
      traceback.print_exc()

    uhdm_dump_log_strm.flush()

  # Go ahead and delete the file if it's too large. CI build tends to run out of disk space.
  if os.path.isfile(uhdm_dump_log_filepath) and \
      os.path.getsize(uhdm_dump_log_filepath) > (128 * 1024 * 1024):
    os.remove(uhdm_dump_log_filepath)

  end_dt = datetime.now()
  delta = end_dt - start_dt
  print(f'end-time: {str(end_dt)} {str(delta)}')

  return {
    'STATUS': status,
    # 'WALL-TIME': delta  # Don't overwrite the time. We aren't tracking uhdm-dump times
  }

def _run_roundtrip(
    name, filepath, roundtrip_filepath, uhdm_src_filepath, roundtrip_log_filepath, output_dirpath):
  start_dt = datetime.now()
  print(f'start-time: {start_dt}')

  status = Status.PASS
  roundtrip_args = [
    roundtrip_filepath,
    '-uhdm-mode', _transform_path(uhdm_src_filepath),
    '-base', _transform_path(os.path.dirname(filepath)),
    '-log', _transform_path(output_dirpath)
  ]

  print('Launching roundtrip with arguments:')
  pprint.pprint(roundtrip_args)
  print('\n')

  with open(roundtrip_log_filepath, 'wt', encoding='cp850') as roundtrip_log_strm:
    try:
      result = subprocess.run(
          roundtrip_args,
          stdout=roundtrip_log_strm,
          stderr=subprocess.STDOUT,
          check=False,
          cwd=os.path.dirname(roundtrip_filepath))
      print(f'roundtrip terminated with exit code: {result.returncode}')
    except:
      status = Status.FAILDUMP
      print(f'roundtrip threw an exception')
      traceback.print_exc()

    roundtrip_log_strm.flush()

  # Go ahead and delete the file if it's too large. CI build tends to run out of disk space.
  if os.path.isfile(roundtrip_log_filepath) and \
      os.path.getsize(roundtrip_log_filepath) > (128 * 1024 * 1024):
    os.remove(roundtrip_log_filepath)

  end_dt = datetime.now()
  delta = end_dt - start_dt
  print(f'end-time: {str(end_dt)} {str(delta)}')

  return {
    'STATUS': status,
    # 'WALL-TIME': delta  # Don't overwrite the time. We aren't tracking uhdm-dump times
  }


def _compare_one(lhs_filepath, rhs_filepath, prefilter=lambda x: x):
  lhs_content = [prefilter(line) for line in open(lhs_filepath, 'rt', encoding='cp850').readlines()]
  rhs_content = [prefilter(line) for line in open(rhs_filepath, 'rt', encoding='cp850').readlines()]
  return [line for line in difflib.unified_diff(lhs_content, rhs_content, fromfile=lhs_filepath, tofile=rhs_filepath, n = 0)]


def _run_one(params):
  start_dt = datetime.now()
  name, filepath, workspace_dirpath, surelog_filepath, uhdm_dump_filepath, roundtrip_filepath, mp, mt, tool, output_dirpath = params

  log(f'Running {name} ...')

  dirpath = os.path.dirname(filepath)
  regression_log_filepath = os.path.join(output_dirpath, 'regression.log')
  surelog_log_filepath = os.path.join(output_dirpath, f'{name}.log')
  golden_log_filepath = os.path.join(dirpath, f'{name}.log')
  uvm_reldirpath = os.path.relpath(os.path.join(workspace_dirpath, 'third_party', 'UVM'), dirpath)
  uhdm_slpp_all_filepath = os.path.join(output_dirpath, 'slpp_all', 'surelog.uhdm')
  uhdm_slpp_unit_filepath = os.path.join(output_dirpath, 'slpp_unit', 'surelog.uhdm')
  uhdm_dump_log_filepath = os.path.join(output_dirpath, 'uhdm.dump')
  roundtrip_output_dirpath = os.path.join(output_dirpath, 'roundtrip')
  roundtrip_log_filepath = os.path.join(roundtrip_output_dirpath, 'roundtrip.log')

  _rmdir(output_dirpath)
  _mkdir(output_dirpath)
  _mkdir(roundtrip_output_dirpath)

  result = {
    'TESTNAME': name,
    'STATUS': Status.PASS,
    'diff-lines': [],
    'golden-log-filepath': golden_log_filepath,
    'surelog-log-filepath': surelog_log_filepath,
    'golden': {},
    'current': {}
  }

  with open(regression_log_filepath, 'wt', encoding='cp850') as regression_log_strm, \
          redirect_stdout(regression_log_strm), \
          redirect_stderr(regression_log_strm):
    print(f'start-time: {start_dt}')
    print( '')
    print( 'Environment:')
    print(f'               test-name: {name}')
    print(f'            test-dirpath: {dirpath}')
    print(f'           test-filepath: {filepath}')
    print(f'       workspace-dirpath: {workspace_dirpath}')
    print(f'        surelog-filepath: {surelog_filepath}')
    print(f'      uhdm_dump-filepath: {uhdm_dump_filepath}')
    print(f'          uvm-reldirpath: {uvm_reldirpath}')
    print(f'          output-dirpath: {output_dirpath}')
    print(f'     golden-log-filepath: {golden_log_filepath}')
    print(f'    surelog-log-filepath: {surelog_log_filepath}')
    print(f'  uhdm-slpp_all-filepath: {uhdm_slpp_all_filepath}')
    print(f' uhdm-slpp_unit-filepath: {uhdm_slpp_unit_filepath}')
    print(f'  uhdm-dump-log-filepath: {uhdm_dump_log_filepath}')
    print(f'roundtrip-output-dirpath: {roundtrip_output_dirpath}')
    print(f'  roundtrip_log_filepath: {roundtrip_log_filepath}')
    print(f'                    tool: {tool}')
    print( '\n')

    print('Snapshot ...')
    golden_snapshot = _snapshot_directory_state(dirpath)
    print(f'Found {len(golden_snapshot)} files & directories')
    print('\n')

    print('Running Surelog ...')
    result.update(_run_surelog(
        name, filepath, dirpath, workspace_dirpath, surelog_filepath,
        surelog_log_filepath, uvm_reldirpath, mp, mt, tool, output_dirpath))
    print('\n')
    regression_log_strm.flush()

    uhdm_src_filepath = None
    if result['STATUS'] == Status.PASS:
      if os.path.isfile(uhdm_slpp_all_filepath):
        uhdm_src_filepath = uhdm_slpp_all_filepath
      elif os.path.isfile(uhdm_slpp_unit_filepath):
        uhdm_src_filepath = uhdm_slpp_unit_filepath
      else:
        print(f'File not found: {uhdm_slpp_all_filepath}')
        print(f'File not found: {uhdm_slpp_unit_filepath}')

    if uhdm_src_filepath and result['STATUS'] == Status.PASS:
      print('Running uhdm-dump ...')
      result.update(_run_uhdm_dump(
          name, uhdm_dump_filepath, uhdm_src_filepath, uhdm_dump_log_filepath, output_dirpath))
      print('\n')
      regression_log_strm.flush()

    roundtrip_content = None
    if uhdm_src_filepath and result['STATUS'] == Status.PASS:
      print('Running roundtrip ...')
      result.update(_run_roundtrip(
          name, filepath, roundtrip_filepath, uhdm_src_filepath,
          roundtrip_log_filepath, roundtrip_output_dirpath))
      print('\n')
      regression_log_strm.flush()

      if os.path.isfile(roundtrip_log_filepath):
        roundtrip_content = open(roundtrip_log_filepath, 'rt').read()

    print(f'Normalizing surelog log file {surelog_log_filepath}')
    if os.path.isfile(surelog_log_filepath):
      content = open(surelog_log_filepath, 'rt', encoding='cp850').read()
      if 'Segmentation fault' in content:
        result['STATUS'] = Status.SEGFLT

      if roundtrip_content:
        content += '\n\n' + roundtrip_content

      content = _normalize_log(content, {
        workspace_dirpath: '${SURELOG_DIR}'
      })

      open(surelog_log_filepath, 'wt', encoding='cp850').write(content)
    else:
      print(f'File not found: {surelog_log_filepath}')
      result['STATUS'] == Status.FAIL
    print('\n')

    # If golden file is missing, then fail the test explicitly!
    if result['STATUS'] == Status.PASS and not os.path.isfile(golden_log_filepath):
      result['STATUS'] = Status.NOGOLD

    result.update({
      'golden': _get_log_statistics(golden_log_filepath),
      'current': _get_log_statistics(surelog_log_filepath)
    })

    if result['STATUS'] == Status.PASS:
      current = result['current']
      golden = result['golden']
      if len(current) == len(golden):
        for k, v in current.items():
          if k not in ['ROUNDTRIP_A', 'ROUNDTRIP_B'] and v != golden.get(k, 0):
            result['STATUS'] = Status.DIFF
            break
      else:
        result['STATUS'] = Status.DIFF

    print('Restoring pristine state ...')
    current_snapshot = _snapshot_directory_state(dirpath)
    print(f'Found {len(current_snapshot)} files & directories')

    _restore_directory_state(
      dirpath, golden_snapshot,
      output_dirpath, current_snapshot)
    print('\n')

    if result['STATUS'] == Status.DIFF:
      result['diff-lines'] = _compare_one(golden_log_filepath, surelog_log_filepath)
      regression_log_strm.writelines(result['diff-lines'])

    end_dt = datetime.now()
    delta = end_dt - start_dt
    print(f'end-time: {str(end_dt)} {str(delta)}')

    regression_log_strm.flush()

  return result


def _report_one(params):
  start_dt = datetime.now()
  name, filepath, output_dirpath = params

  log(f'Comparing {name}')

  dirpath = os.path.dirname(filepath)
  golden_log_filepath = os.path.join(dirpath, f'{name}.log')
  surelog_log_filepath = os.path.join(output_dirpath, f'{name}.log')
  report_log_filepath = os.path.join(output_dirpath, 'report.log')

  result = {
    'TESTNAME': name,
    'STATUS': Status.PASS,
    'diff-lines': [],
    'golden-log-filepath': golden_log_filepath,
    'surelog-log-filepath': surelog_log_filepath,
    'golden': {},
    'current': {}
  }

  if not os.path.isdir(dirpath):
    result['STATUS'] = Status.FAIL
    return result

  with open(report_log_filepath, 'wt', encoding='cp850') as report_log_strm, \
      redirect_stdout(report_log_strm), \
      redirect_stderr(report_log_strm):

    print(f'start-time: {start_dt}')
    print( '')
    print( 'Environment:')
    print(f'              test-name: {name}')
    print(f'           test-dirpath: {dirpath}')
    print(f'          test-filepath: {filepath}')
    print(f'    golden-log-filepath: {golden_log_filepath}')
    print(f'   surelog-log-filepath: {surelog_log_filepath}')
    print( '\n')

    # If either output file is missing, then fail the test explicitly!
    if os.path.isfile(surelog_log_filepath) != os.path.isfile(golden_log_filepath):
      result['STATUS'] = Status.FAIL

    result.update({
      'golden': _get_log_statistics(golden_log_filepath),
      'current': _get_log_statistics(surelog_log_filepath)
    })

    if result['STATUS'] == Status.PASS:
      current = result['current']
      golden = result['golden']
      if len(current) == len(golden):
        for k, v in current.items():
          if k not in ['ROUNDTRIP_A', 'ROUNDTRIP_B'] and v != golden.get(k, 0):
            result['STATUS'] = Status.DIFF
            break
      else:
          result['STATUS'] = Status.DIFF

    print('Comparison Result:')
    pprint.pprint(result)
    print('\n')

    if result['STATUS'] == Status.DIFF:
      result['diff-lines'] = _compare_one(golden_log_filepath, surelog_log_filepath)
      report_log_strm.writelines(result['diff-lines'])

    end_dt = datetime.now()
    delta = end_dt - start_dt
    print(f'end-time: {str(end_dt)} {str(delta)}')

    report_log_strm.flush()

  return result


def _update_one(params):
  start_dt = datetime.now()
  name, filepath, output_dirpath = params

  log(f'Updating {name}')

  dirpath = os.path.dirname(filepath)
  golden_log_filepath = os.path.join(dirpath, f'{name}.log')
  surelog_log_filepath = os.path.join(output_dirpath, f'{name}.log')

  if not os.path.isfile(surelog_log_filepath):
    print(f'File not found: {surelog_log_filepath}')
  else:
    try:
      if os.path.isfile(golden_log_filepath):
        os.remove(golden_log_filepath)

      shutil.copy(surelog_log_filepath, golden_log_filepath)

      # lines = []
      # with open(surelog_log_filepath, 'rt', encoding='cp850') as istrm:
      #   for line in istrm:
      #     line = line.rstrip('\n')
      #     line = line.replace('/regression/', '/tests/')
      #     lines.append(line)
      #   istrm.close()
      #
      # while not lines[-1]:
      #   lines = lines[:-1]
      # lines.append('')
      #
      # with open(golden_log_filepath, 'wt', encoding='cp850') as ostrm:
      #   for line in lines:
      #     ostrm.write(line)
      #     ostrm.write('\n')
      #   ostrm.flush()
      #   ostrm.close()
    except:
      print(f'Failed to overwrite \"{golden_log_filepath}\" with \"{surelog_log_filepath}\"')
      traceback.print_exc()
      return 1

  return 0


def _print_report(results):
  columns = ['TESTNAME', 'STATUS', 'FATAL', 'SYNTAX', 'ERROR', 'WARNING', 'NOTE', 'WALL-TIME', 'CPU-TIME', 'VTL-MEM', 'PHY-MEM', 'ROUNDTRIP']

  rows = []
  summary = OrderedDict([(status.name, 0) for status in Status])
  for result in results:
    current = result['current']
    golden = result['golden']

    def _get_cell_value(name):
      if golden and current.get(name, 0) != golden.get(name, 0):
        return f'{current.get(name, 0)} ({current.get(name, 0) - golden.get(name, 0)})'
      else:
        return f'{current.get(name, 0)}'

    summary[result[columns[1]].name] += 1
    rows.append([
      result[columns[0]],
      result[columns[1]].name,
      _get_cell_value(columns[2]),
      _get_cell_value(columns[3]),
      _get_cell_value(columns[4]),
      _get_cell_value(columns[5]),
      _get_cell_value(columns[6]),
      str(round(result.get(columns[7], timedelta(seconds=0)).total_seconds())),
      str(round(result.get(columns[8], 0))),
      str(round(result.get(columns[9], 0) / (1024 * 1024))),
      str(round(result.get(columns[10], 0) / (1024 * 1024))),
      '{}/{}'.format(_get_cell_value("ROUNDTRIP_A"), _get_cell_value("ROUNDTRIP_B")),
    ])

  longest_test = max(results, key=lambda result: result.get('WALL-TIME', 0))
  summary['LONGEST TEST'] = longest_test['TESTNAME']
  summary['MAX TIME'] = str(round(longest_test['WALL-TIME'].total_seconds()))

  largest_test = max(results, key=lambda result: result.get('PHY-MEM', 0))
  summary['LARGEST TEST'] = largest_test['TESTNAME']
  summary['MAX MEMORY'] = str(round(largest_test['PHY-MEM'] / (1024 * 1024)))

  widths = [max([len(row[index]) for row in [columns] + rows]) for index in range(0, len(columns))]
  row_format = '  | ' + ' | '.join([f'{{:{width}}}' for width in widths]) + ' |'
  separator = '  +-' + '-+-'.join(['-' * width for width in widths]) + '-+'

  print('Results: ')
  print(separator)
  print(row_format.format(*columns))
  print(separator)
  for row in rows:
    print(row_format.format(*row))
  print(separator)

  return summary


def _print_diffs(results):
  max_lines_per_result = 50
  for result in results:
    if result['STATUS'] == Status.DIFF:
      print('=' * 120)
      print(f'diff {result["golden-log-filepath"]} {result["surelog-log-filepath"]}')
      sys.stdout.writelines(result['diff-lines'][:max_lines_per_result])
      if len(result['diff-lines']) > max_lines_per_result:
        print(f'... and {len(result["diff-lines"]) - max_lines_per_result} more.')
      print('\n\n')


def _print_summary(summary):
  rows = [[k, str(v)] for k, v in summary.items()]
  widths = [max([len(str(row[index])) for row in rows]) for index in range(0, 2)]
  row_format = '  | ' + ' | '.join([f'{{:{width}}}' for width in widths]) + ' |'
  separator = '  +-' + '-+-'.join(['-' * width for width in widths]) + '-+'

  print('Summary: ')
  print(separator)
  for row in rows:
    print(row_format.format(*row))
  print(separator)


def _run(args, tests):
  if not tests:
    return 0  # No selected tests

  params = [(
    name,
    filepath,
    args.workspace_dirpath,
    args.surelog_filepath,
    args.uhdm_dump_filepath,
    args.roundtrip_filepath,
    args.mp,
    args.mt,
    args.tool,
    os.path.join(args.output_dirpath, name)
  ) for name, filepath in tests.items()]

  if args.jobs == 0:
    results = [_run_one(param) for param in params]
  else:
    with multiprocessing.Pool(processes=args.jobs) as pool:
      results = pool.map(_run_one, params)

  print('\n\n')
  summary = _print_report(results)

  if args.show_diffs:
    print('\n\n')
    _print_diffs(results)

  print('\n\n')
  _print_summary(summary)

  result = sum([entry['STATUS'].value for entry in results])
  return result


def _report(args, tests):
  if not tests:
    return 0  # No selected tests

  params = [(
    name,
    filepath,
    os.path.join(args.output_dirpath, name)
  ) for name, filepath in tests.items()]

  if args.jobs == 0:
    results = [_report_one(param) for param in params]
  else:
    with multiprocessing.Pool(processes=args.jobs) as pool:
      results = pool.map(_report_one, params)

  print('\n\n')
  summary = _print_report(results)
  print('\n\n')

  if args.show_diffs:
    _print_diffs(results)
    print('\n\n')

  _print_summary(summary)

  return 0


def _update(args, tests):
  if not tests:
    return 0  # No selected tests

  params = [(
    name,
    filepath,
    os.path.join(args.output_dirpath, name)
  ) for name, filepath in tests.items()]

  if args.jobs == 0:
    results = [_update_one(param) for param in params]
  else:
    with multiprocessing.Pool(processes=args.jobs) as pool:
      results = pool.map(_update_one, params)

  return sum(results)


def _main():
  # Configure the standard streams to be unicode compatible
  sys.stdout.reconfigure(encoding='cp850')
  sys.stderr.reconfigure(encoding='cp850')

  start_dt = datetime.now()
  print(f'Starting Surelog Regression Tests @ {str(start_dt)}')

  parser = argparse.ArgumentParser()

  parser.add_argument(
      'mode', choices=['run', 'report', 'update'], type=str, help='Pick from available choices')
  parser.add_argument(
      '--workspace-dirpath', dest='workspace_dirpath', required=False, default=_default_workspace_dirpath, type=str,
      help='Workspace root, either absolute or relative to current working directory.')
  parser.add_argument(
      '--test-dirpaths', dest='test_dirpaths', required=False, default=_default_test_dirpaths, nargs='*', type=str,
      help='Directories, either absolute or relative to workspace directory, to scan for tests.')
  parser.add_argument(
      '--output-dirpath', dest='output_dirpath', required=False, default=_default_output_dirpath, type=str,
      help='Output directory path, either absolute or relative to the workspace directory.')
  parser.add_argument(
      '--build-dirpath', dest='build_dirpath', required=False, default=_default_build_dirpath, type=str,
      help='Directory, either absolute or relative to workspace directory, to locate surelog binary')
  parser.add_argument(
      '--surelog-filepath', dest='surelog_filepath', required=False, default=_default_surelog_filepath, type=str,
      help='Location, either absolute or relative to build directory, of surelog executable')
  parser.add_argument(
      '--uhdm-dump-filepath', dest='uhdm_dump_filepath', required=False, default=_default_uhdm_dump_filepath, type=str,
      help='Location, either absolute or relative to build directory, of uhdm-dump executable')
  parser.add_argument(
      '--roundtrip-filepath', dest='roundtrip_filepath', required=False, default=_default_roundtrip_filepath, type=str,
      help='Location, either absolute or relative to build directory, of roundtrip executable')
  parser.add_argument(
      '--filters', nargs='+', required=False, default=[], type=str, help='Filter tests matching these regex inputs')
  parser.add_argument(
      '--jobs', nargs='?', required=False, default=multiprocessing.cpu_count(), type=int,
      help='Run tests in parallel, optionally providing max number of concurrent processes. Set 0 to run sequentially.')
  parser.add_argument(
      '--show-diffs', dest='show_diffs', required=False, default=False, action='store_true',
      help='Show file differences when applicable.')
  parser.add_argument(
      '--tool', dest='tool', choices=['ddd', 'valgrind'], required=False, default=None, type=str,
      help='Run regression test using specified tool.')
  parser.add_argument('--mt', dest='mt', default=0, type=int, help='Enable multithreading mode')
  parser.add_argument('--mp', dest='mp', default=0, type=int, help='Enable multiprocessing mode')

  args = parser.parse_args()

  if (args.jobs == None) or (args.jobs > multiprocessing.cpu_count()):
    args.jobs = multiprocessing.cpu_count()

  if not os.path.isabs(args.workspace_dirpath):
    args.workspace_dirpath = os.path.abspath(args.workspace_dirpath)

  if not os.path.isabs(args.build_dirpath):
    args.build_dirpath = os.path.join(args.workspace_dirpath, args.build_dirpath)
  args.build_dirpath = os.path.abspath(args.build_dirpath)

  if not os.path.isabs(args.surelog_filepath):
    args.surelog_filepath = os.path.join(args.build_dirpath, args.surelog_filepath)
  args.surelog_filepath = os.path.abspath(args.surelog_filepath)

  if not os.path.isabs(args.uhdm_dump_filepath):
    args.uhdm_dump_filepath = os.path.join(args.build_dirpath, args.uhdm_dump_filepath)
  args.uhdm_dump_filepath = os.path.abspath(args.uhdm_dump_filepath)

  if not os.path.isabs(args.roundtrip_filepath):
    args.roundtrip_filepath = os.path.join(args.build_dirpath, args.roundtrip_filepath)
  args.roundtrip_filepath = os.path.abspath(args.roundtrip_filepath)

  if not os.path.isabs(args.output_dirpath):
    args.output_dirpath = os.path.join(args.build_dirpath, args.output_dirpath)
  args.output_dirpath = os.path.abspath(args.output_dirpath)

  args.test_dirpaths = [
    os.path.abspath(dirpath if os.path.isabs(dirpath) else os.path.join(args.workspace_dirpath, dirpath))
    for dirpath in args.test_dirpaths
  ]

  args.filters = [text if text.isalnum() else re.compile(text, re.IGNORECASE) for text in args.filters]
  all_tests, filtered_tests, blacklisted_tests = _scan(args.test_dirpaths, args.filters)

  print( 'Environment:')
  print(f'      command-line: {" ".join(sys.argv)}')
  print(f'   current-dirpath: {os.getcwd()}')
  print(f' workspace-dirpath: {args.workspace_dirpath}')
  print(f'     build-dirpath: {args.build_dirpath}')
  print(f'  surelog-filepath: {args.surelog_filepath}')
  print(f'uhdm-dump-filepath: {args.uhdm_dump_filepath}')
  print(f'roundtrip-filepath: {args.roundtrip_filepath}')
  print(f'     test-dirpaths: {"; ".join(args.test_dirpaths)}')
  print(f'    output-dirpath: {args.output_dirpath}')
  print(f'   multi-threading: {args.mt}')
  print(f'  multi-processing: {args.mp}')
  print(f'          max-jobs: {args.jobs}')
  print(f'         max-tests: {len(all_tests)}')
  print(f' blacklisted-tests: {len(blacklisted_tests)}')
  print(f'    filtered-tests: {len(filtered_tests)}')
  print( '\n\n')

  _mkdir(args.output_dirpath)

  result = 0
  if args.mode == 'run':
    print(f'Running {len(filtered_tests)} tests ...')
    result = _run(args, filtered_tests)
  elif args.mode == 'report':
    print(f'Reporting {len(filtered_tests)} tests ...')
    result = _report(args, filtered_tests)
  elif args.mode == 'update':
    print(f'Updating {len(filtered_tests)} tests ...')
    result = _update(args, filtered_tests)
  print('\n\n')

  end_dt = datetime.now()
  delta = round((end_dt - start_dt).total_seconds())
  print(f'Surelog Regression Test Completed @ {str(end_dt)} in {str(delta)} seconds')
  return result


if __name__ == '__main__':
  sys.exit(_main())
