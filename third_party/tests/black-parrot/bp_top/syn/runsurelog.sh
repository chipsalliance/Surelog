#!/bin/bash
{ # try
   rm -rf results/ simsc/slpp_all
   make build_cov.sc sim.sc SUITE=riscv_tests PROG=rsort
   rm -rf results/ simsc/slpp_all
   make build_cov.sc sim.sc SUITE=riscv_tests PROG=rsort VERILATOR="$1 -sverilog -parse -nopython -verbose -timescale=1ps/1ps -elabuhdm -d coveruhdm -verbose"  && echo "OK"
    #save your output

} || { # catch
    # save log for exception
    echo "OK"
}
