# Utilities used to compare Verilator and Surelog hierarchy

* 1) verilator.tcl takes a xxx_expand.tree from Verilator obtained with the --dump-tree and extracts the hierarchy paths

* 2) Use Surelog/build/third_party/bin/uhdm-hier surelog.uhdm to dump Surelog hierarchy
* sort.tcl lexical sort Surelog output

* 3) diff.tcl <from> <to> displays missing entries in <to> taken from <from>
