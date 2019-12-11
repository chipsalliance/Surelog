#!/bin/bash

make RISCV=blah verilator="$1 -noinfo -nonote -parse -noelab -timescale=1ps/1ps" verilate CFLAGS="" LDFLAGS=""
