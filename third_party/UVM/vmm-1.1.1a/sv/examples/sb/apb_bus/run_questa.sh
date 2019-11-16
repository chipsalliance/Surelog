#!/bin/sh


if [ -z "$VMM_HOME" ] ; then
VMM_HOME=../../../..
fi

if [ -z "$VMM_DPI_DIR" ] ; then
VMM_DPI_DIR=$VMM_HOME/shared/lib/linux_x86_64
fi

if [ "$1" = clean ] ; then
  rm -rf *.log *.log.filtered *.wlf transcript* work; exit
fi


vlib work
vlog -mfcu -sv +incdir+$VMM_HOME/sv+. +incdir+apb test_simple.sv tb_top.sv | tee test_simple.log
if [ $? -eq 0 ]; then
  vsim -c -do "set SolveArrayResizeMax 5000; run -all; quit" -sv_lib $VMM_DPI_DIR/vmm_str_dpi \
    +vmm_log_default=trace tb_top test_simple -l test_simple.log
fi

# internal use only
EX=$VMM_HOME/sv/examples
if [ -n "$INTEROP_REGRESS" ] ; then
  perl $EX/regress/regress_passfail.pl test_simple.log  "sb/apb_bus" $EX/results.log
fi

