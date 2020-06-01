#!/bin/bash

make RISCV=blah verilator="$1 -sverilog -parse -d coveruhdm -verbose -timescale=1ps/1ps" verilate CFLAGS="" LDFLAGS=""
