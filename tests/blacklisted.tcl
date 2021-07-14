set WINDOWS_BLACK_LIST [dict create]
dict set WINDOWS_BLACK_LIST Ariane 1
dict set WINDOWS_BLACK_LIST BlackParrot 1
dict set WINDOWS_BLACK_LIST BlackPBe 1
dict set WINDOWS_BLACK_LIST BlackUnicore 1
dict set WINDOWS_BLACK_LIST BlackUcode 1
dict set WINDOWS_BLACK_LIST CoresSweRV 1
dict set WINDOWS_BLACK_LIST SimpleIncludeAndMacros 1
dict set WINDOWS_BLACK_LIST TestFileSplit 1
dict set WINDOWS_BLACK_LIST UnitElabExternNested 1
dict set WINDOWS_BLACK_LIST UnitPython 1
dict set WINDOWS_BLACK_LIST UnitSimpleIncludeAndMacros 1
dict set WINDOWS_BLACK_LIST Verilator 1
dict set WINDOWS_BLACK_LIST BuildUVMPkg 1
dict set WINDOWS_BLACK_LIST Compl1001 1
dict set WINDOWS_BLACK_LIST YosysOpenSparc 1
dict set WINDOWS_BLACK_LIST Earlgrey_Verilator_0_1 1
dict set WINDOWS_BLACK_LIST Earlgrey_Verilator_01_05_21 1
dict set WINDOWS_BLACK_LIST Earlgrey_nexysvideo 1

set UNIX_BLACK_LIST [dict create]
# 2 message diff:
dict set UNIX_BLACK_LIST UnitElabExternNested 1

# RAM size in CI machines
dict set UNIX_BLACK_LIST Earlgrey_nexysvideo 1
dict set UNIX_BLACK_LIST BlackParrot 1
dict set UNIX_BLACK_LIST BlackPBe 1
dict set UNIX_BLACK_LIST BlackUnicore 1
dict set UNIX_BLACK_LIST BlackUcode 1
