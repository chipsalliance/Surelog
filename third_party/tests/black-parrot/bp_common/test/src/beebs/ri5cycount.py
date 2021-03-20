#!/usr/bin/env python3

from subprocess import Popen, PIPE, TimeoutExpired
import codecs
import logging
import os
import sys

benchmarks = (
     'aha-compress', 'aha-mont64', 'bs', 'bubblesort', 'cnt', 'compress',
     'cover', 'crc', 'crc32', 'ctl-stack', 'ctl-string', 'ctl-vector',
     'cubic', 'dijkstra', 'dtoa', 'duff', 'edn', 'expint', 'fac', 'fasta',
     'fdct', 'fibcall', 'fir', 'frac', 'huffbench', 'insertsort',
     'janne_complex', 'jfdctint', 'lcdnum', 'levenshtein', 'ludcmp', 'matmult',
     'matmult-float', 'matmult-int', 'mergesort', 'miniz', 'minver', 'nbody',
     'ndes', 'nettle-arcfour', 'nettle-cast128', 'nettle-des', 'nettle-md5',
     'newlib-exp', 'newlib-log', 'newlib-mod', 'newlib-sqrt', 'ns', 'nsichneu',
     'picojpeg', 'prime', 'qrduino', 'qsort', 'qurt', 'recursion', 'rijndael',
     'select', 'sglib-arraybinsearch', 'sglib-arrayheapsort',
     'sglib-arrayquicksort', 'sglib-arraysort', 'sglib-dllist',
     'sglib-hashtable', 'sglib-listinsertsort', 'sglib-listsort', 'sglib-queue',
     'sglib-rbtree', 'slre', 'sqrt', 'st', 'statemate', 'stb_perlin',
     'stringsearch1', 'strstr', 'tarai', 'template', 'trio', 'trio-snprintf',
     'trio-sscanf', 'ud', 'whetstone', 'wikisort'
)

# Commands sent to GDB. In order to avoid complicated interaction with GDB,
# we just shove everything into the buffer and then read everything out
# and wait for termination (with the Popen.communicate() method). This works
# because we don't have too much input, but adding more might result in
# blocking / deadlock (possibly - I have not checked whether Popen.write()
# could risk this).

commands = [
    b'-target-select remote :51000',
    b'load',
    b'set $start = start_trigger',
    b'set $stop = stop_trigger',
    b'-break-insert *$start',
    b'-break-insert *$stop',
    b'-break-insert exit',
    b'cont',
    b'-interpreter-exec console "monitor cyclecount"',
    b'cont',
    b'-interpreter-exec console "monitor cyclecount"',
    b'cont',
    b'-interpreter-exec console "monitor exit"',
    b'quit'
]

# Set up logging
log = logging.getLogger()

def setup_logging(logfile):
    log.setLevel(logging.DEBUG)
    ch = logging.StreamHandler(sys.stdout)
    ch.setLevel(logging.INFO)
    log.addHandler(ch)
    fh = logging.FileHandler(logfile)
    fh.setLevel(logging.DEBUG)
    log.addHandler(fh)

class GdbParsingError(RuntimeError):
    """Exception raised for errors in parsing interactions with gdb."""

    def __init__(self, message):
        self.message = message
        super().__init__(message)

def execute(executable, commands):
    gdbservercmd = ['riscv32-gdbserver', '-c', 'ri5cy', '51000']
    log.debug('\nLaunching GDB server...')
    gdbserver = Popen(gdbservercmd, stdout=PIPE, stderr=PIPE, stdin=PIPE)

    gdbcmd = ['riscv32-unknown-elf-gdb', '--interpreter=mi', \
        executable]
    log.debug('\nLaunching gdb...')
    debugger = Popen(gdbcmd, stdin=PIPE, stdout=PIPE, stderr=PIPE)

    log.debug('\nCommunicating with gdb...')
    # Handle timeouts as prescribed in:
    # https://docs.python.org/3/library/subprocess.html#subprocess.Popen.communicate
    try:
        stdout, stderr = debugger.communicate(input=b'\n'.join(commands),
            timeout=240)
        log.debug('\n... Finished communicating with gdb.')
    except TimeoutExpired:
        log.debug('\nExecution failed - timeout reached.')
        debugger.kill()
        stdout, stderr = debugger.communicate()
    except GdbParsingError as gpe:
        log.debug('Error parsing output from GDB: %s' % gpe.message)

    log.debug('\nStandard output from gdb:\n')
    log.debug(codecs.decode(stdout, 'utf-8'))
    log.debug('\nStandard error from gdb:\n')
    log.debug(codecs.decode(stderr, 'utf-8'))

    gdb_output = stdout.decode()

    log.debug('\nKilling gdbserver...')
    log.debug('gdbserver return code %s' % gdbserver.returncode)
    stdout, stderr = gdbserver.communicate(input='', timeout=10)

    gdbserver_output = stdout.decode()

    log.debug('\nStandard output from gdbserver:\n')
    log.debug(gdbserver_output)
    log.debug('\nStandard error from gdbserver:\n')
    log.debug(stderr.decode())

    return gdb_output

def parse_output(output):
    seen_start = False
    seen_stop = False
    seen_exit = False
    lines = output.split('\n')
    for i, line in enumerate(lines):
        #print(line)
        if not seen_start:
            if "in start_trigger" in line:
                start = lines[i+4]
                start = int(start.split('"')[1].strip('\\n'))
                seen_start = True

        if not seen_stop:
            if "in stop_trigger" in line:
                stop = lines[i+4]
                stop = int(stop.split('"')[1].strip('\\n'))
                seen_stop = True

        if not seen_exit:
            if "exit (code=" in line:
                exit_code = line.split()[3].strip().split('=')[1].split(')')[0]
                seen_exit = True

    if not seen_start:
        raise GdbParsingError('Did not find start trigger cycle count')

    if not seen_stop:
        raise GdbParsingError('Did not find stop trigger cycle count')

    if not seen_exit:
        raise GdbParsingError('Did not find exit code')

    cycle_count = stop - start
    return cycle_count, exit_code

def run_benchmark(bm):
    executable = os.path.join('src', bm, bm)
    try:
        output = execute(executable, commands)
        #print(output)
        cycle_count, exit_code = parse_output(output)
    except GdbParsingError as gpe:
        log.debug('Error parsing output from GDB for %s: %s' % (bm, gpe.message))
        cycle_count = -1
        exit_code = -1
    except TimeoutExpired:
        log.debug('Timeout expired for %s' % bm)
        cycle_count = -2
        exit_code = -2

    print('%s,%s,%s' % (bm, cycle_count, exit_code))

def run_benchmarks():
    setup_logging('beebs-riscv32.log')
    for bm in benchmarks:
        run_benchmark(bm)

if __name__ == '__main__':
    sys.exit(run_benchmarks())
