import os
import platform

# If you are adding a new entry, please include a short comment
# explaining why the specific test is blacklisted.


_windows_black_list = set([name.lower() for name in [
    r'ariane',
    r'blackparrot',
    r'blackucode',
    r'blackunicore',
    r'builduvmpkg',
    r'compl1001',
    r'coresswerv',
    r'earlgrey_nexysvideo',
    r'earlgrey_verilator_0_1',
    r'earlgrey_verilator_01_05_21', # lowmem is unsupported
    r'lpddr',
    r'simpleincludeandmacros',
    r'simpleparsertestcache', # race condition
    r'testfilesplit',
    r'testsepcompnohash',     # Uses shell script to run
    r'unitelabexternnested',
    r'unitpython',
    r'unitsimpleincludeandmacros',
    r'verilator',
    r'yosysopensparc',
    r'testnohash'
]])

_unix_black_list = set([name.lower() for name in [
    r'blackparrot',
    r'blackucode',
    r'blackunicore',
    r'lpddr',
    r'simpleparsertestcache', # race condition
    r'earlgrey_nexysvideo',   # ram size in ci machines
    r'unitelabexternnested',  # 2 message diff:
]])

_msys2_black_list = _unix_black_list.union([
  r'earlgrey_verilator_01_05_21', # lowmem is unsupported
])

_unix_ci_black_list = _unix_black_list.union(set([name.lower() for name in [
    'rsd' # Temporarily disabled on CI as this test seems to be stalling
]]))

def is_blacklisted(name):
    if platform.system() == 'Windows':
        blacklist = _msys2_black_list if 'MSYSTEM' in os.environ else _windows_black_list
    else:
        blacklist = _unix_ci_black_list if 'GITHUB_JOB' in os.environ else _unix_black_list
    return name.lower() in blacklist
