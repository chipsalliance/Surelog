import os
import platform

# If you are adding a new entry, please include a short comment
# explaining why the specific test is blacklisted.

_unix_black_list = set([name.lower() for name in [
  'blackparrot',
  'blackucode',
  'blackunicore',
  'earlgrey_nexysvideo',   # ram size in ci machines
  'lpddr',
  'simpleparsertestcache', # race condition
]])

_windows_black_list = _unix_black_list.union(set([name.lower() for name in [
  'ariane',                       # Uses shell script with make command
  'earlgrey_verilator_01_05_21',  # lowmem is unsupported
  'unitpython',                   # Python is unsupported
]]))

_msys2_black_list = _unix_black_list.union(set([name.lower() for name in [
  'earlgrey_verilator_01_05_21', # lowmem is unsupported
]]))


def is_blacklisted(name):
  if platform.system() == 'Windows':
    blacklist = _msys2_black_list if 'MSYSTEM' in os.environ else _windows_black_list
  else:
    blacklist = _unix_black_list
  return name.lower() in blacklist
