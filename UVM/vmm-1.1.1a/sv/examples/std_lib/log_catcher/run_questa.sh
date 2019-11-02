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
vlog -mfcu -sv +incdir+$VMM_HOME/sv+. \
               +incdir+../vmm_test/verif \
               +define+ALU_BUG1 \
               +define+INTEROP_REGRESS \
               alu_test.sv \
               ../vmm_test/rtl/alu.v \
               ../vmm_test/verif/alu_tb_top.sv | tee alu_test.log
if [ $? -eq 0 ]; then
  vsim -c -do "set SolveArrayResizeMax 5000; run -all; quit" \
    -sv_lib $VMM_DPI_DIR/vmm_str_dpi alu_tb_top -l alu_test.log
fi	



# internal use only
EX=$VMM_HOME/sv/examples
if [ -n "$INTEROP_REGRESS" ] ; then
  perl $EX/regress/regress_passfail.pl alu_test.log "std_lib/log_catcher" $EX/results.log
fi
