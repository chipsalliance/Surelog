#!/usr/bin/env bash
{ # try
   rm -rf results/verilator/bp_tethered.e_bp_multicore_1_cfg.none.build/multicore
   make build.sc CFG=e_bp_multicore_1_cfg VERILATOR="$1 -DVERILATOR=1 -sverilog -parse -nopython -verbose -timescale=1ps/1ps -elabuhdm -d coveruhdm -d uhdmstats -verbose -lowmem -o multicore"  && echo "OK"
    #save your output

} || { # catch
    # save log for exception
    echo "OK"
}
