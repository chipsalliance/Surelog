#!/usr/bin/env python

"""
Script to scan a directory looking for test logs and collect integration errors.
"""

import argparse
from collections import defaultdict
import concurrent.futures
import os
import tarfile
import traceback
import zipfile
from pathlib import Path


_platform_ids = ['.linux', '.osx', '.msys', '.win', '']
_zip_file_count = 8
_zip_filename_pattern = 'sl-linux-gcc-release-regression-{index}.zip'
_tar_filename_pattern = 'sl-linux-gcc-release-regression-{index}.tar.gz'


def _is_ci_build():
  return 'GITHUB_JOB' in os.environ


def _merge_dicts(dicta, dictb):
  return {
    key: dicta.get(key, 0) + dictb.get(key, 0)
    for key in set(dicta.keys()).union(set(dictb.keys()))
  }


def _scan_tar(tarfile_strm):
  errors = []
  counts = defaultdict(int)
  categories = {}
  with tarfile.open(fileobj=tarfile_strm) as archive_strm:
    for test_archive_path in archive_strm.getnames():
      test_archive_name = Path(Path(test_archive_path).stem).stem
          
      with tarfile.open(fileobj=archive_strm.extractfile(test_archive_path)) as test_archive_strm:
        for platform_id in _platform_ids:
          src_filepath = f'{test_archive_name}/{test_archive_name}{platform_id}.log'

          if src_filepath in test_archive_strm.getnames():
            try:
              src_strm = test_archive_strm.extractfile(src_filepath)
                  
              for line in src_strm:
                line = line.decode().rstrip()
                if line.startswith("[ERR:IG"):
                  errors.append(f"{test_archive_name}: {line}")
                  counts[test_archive_name] += 1

                  category = line[:12]
                  categories[category] = categories.get(category, 0) + 1
                elif line.startswith("Internal Error("):
                  errors.append(f"{test_archive_name}: {line}")
                  categories["[  Internal]"] = categories.get(category, 0) + 1

            except Exception:
              print(f"Failed to parse {src_filepath}")
              traceback.print_last()

  return errors, categories, counts


def _scan_zip(zip_filepath):
  archive_name = Path(zip_filepath).stem
  
  with zipfile.ZipFile(zip_filepath, 'r') as zipfile_strm:
    with zipfile_strm.open(f'{archive_name}.tar.gz') as tarfile_strm:
      return _scan_tar(tarfile_strm)


def _scan_gzip(tar_filepath):
  with open(tar_filepath, 'rb') as tarfile_strm:
    return _scan_tar(tarfile_strm)


def _main():
  parser = argparse.ArgumentParser()
  parser.add_argument('input_dirpath', type=str, help='Directory to scan')
  args = parser.parse_args()
  
  input_dirpath = Path(args.input_dirpath)
  output_filepath = input_dirpath / f"sl-ic-errors.txt"

  filename_pattern = _tar_filename_pattern if _is_ci_build() else _zip_filename_pattern
  scanner = _scan_gzip if _is_ci_build() else _scan_zip
  input_filepaths = [input_dirpath / filename_pattern.format(index=i) for i in range(4)]

  max_workers = len(input_filepaths)
  errors = []
  categories = {}
  counts = defaultdict(int)

  if max_workers == 0:
    for filepath in input_filepaths:
      errs, cats, cts = scanner(filepath)
      errors.extend(errs)
      categories = _merge_dicts(categories, cats)
      counts.update(cts)
  else:
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers*2) as executor:
      for errs, cats, cts in executor.map(scanner, input_filepaths):
        errors.extend(errs)
        categories = _merge_dicts(categories, cats)
        counts.update(cts)

  separator = '\n' + ('=' * 160) + '\n'
  with output_filepath.open("w") as strm:
    strm.write("\n".join(sorted(errors)))
    strm.write(separator)

    strm.write("\n".join(f"{name:>40}: {counts[name]:>6}" for name in sorted(counts.keys())))
    strm.write(separator)

    strm.write("\n".join(f"{category}: {categories[category]:>6}" for category in sorted(categories.keys())))
    strm.write(f"\nFound {len(errors)} total errors.")
    strm.write(separator)

    strm.flush()

  return 0


if __name__ == '__main__':
  import sys
  sys.exit(_main())
