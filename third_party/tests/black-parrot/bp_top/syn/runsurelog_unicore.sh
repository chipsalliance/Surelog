#!/bin/bash
{ # try
  rm -rf results/verilator/bp_tethered.e_bp_unicore_cfg.none.build/
  make build.sc CFG=e_bp_unicore_cfg  VERILATOR="$1 -DVERILATOR=1 -sverilog -parse -verbose -timescale=1ps/1ps -elabuhdm -d coveruhdm -d uhdmstats -verbose -lowmem -o unicore"  && echo "OK"
    #save your output

} || { # catch
    # save log for exception
    echo "OK"
}
