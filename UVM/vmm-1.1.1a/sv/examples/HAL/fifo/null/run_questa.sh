#!/bin/sh

if [ -z "$VMM_HOME" ] ; then
VMM_HOME=../../../../..
fi

if [ -z "$VMM_DPI_DIR" ] ; then
VMM_DPI_DIR=$VMM_HOME/shared/lib/linux_x86_64
fi

if [ "$1" = clean ] ; then
  rm -rf *.log *.log.filtered *.wlf transcript* work; exit
fi

vlib work
vlog -mfcu -sv \
     +incdir+$VMM_HOME/sv+.  \
     +define+VMM_HW_ARCH_NULL \
     +incdir+..+$VMM_HOME/shared/examples/syn_tb_fifo+$VMM_HOME/sv/HAL \
     ../test.sv | tee test.log
if [ $? -eq 0 ]; then
  vsim -c -do "set SolveArrayResizeMax 5000; run -all; quit" \
    -sv_lib $VMM_DPI_DIR/vmm_str_dpi vmm_hw tb_top test -l test.log 
fi

# internal use only
EX=$VMM_HOME/sv/examples
if [ -n "$INTEROP_REGRESS" ] ; then
  perl $EX/regress/regress_passfail.pl test.log "HAL/fifo/null" $EX/results.log
fi

