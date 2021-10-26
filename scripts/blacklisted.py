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
    r'earlgrey_verilator_01_05_21',
    r'lpddr',
    r'simpleincludeandmacros',
    r'simpleparsertestcache', # race condition
    r'testfilesplit',
    r'unitelabexternnested',
    r'unitpython',
    r'unitsimpleincludeandmacros',
    r'verilator',
    r'yosysopensparc',
]])

_unix_black_list = set([name.lower() for name in [
    r'blackparrot',
    r'blackucode',
    r'blackunicore',
    r'lpddr',
    r'simpleparsertestcache',  # race condition
    r'earlgrey_nexysvideo',  # ram size in ci machines
    r'unitelabexternnested', # 2 message diff:
]])


def is_blacklisted(name):
    blacklist = _windows_black_list if platform.system() == 'Windows' else _unix_black_list
    return name.lower() in blacklist
