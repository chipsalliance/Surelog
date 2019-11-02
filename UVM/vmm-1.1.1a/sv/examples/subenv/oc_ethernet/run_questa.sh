#!/bin/sh

if [ -z "$VMM_HOME" ] ; then
VMM_HOME=../../../..
fi

if [ -z "$VMM_DPI_DIR" ] ; then
VMM_DPI_DIR=$VMM_HOME/shared/lib/linux_x86_64
fi

if [ "$1" = clean ] ; then
  rm -rf *.log *.log.filtered *.wlf transcript* work questa.do ral_oc_ethernet.sv ral_dual_eth.sv; exit
fi


echo "set SolveArrayResizeMax 5000; run -all; quit" > questa.do

VLOG_ARGS="-mfcu -sv +define+OC_ETHERNET_BUG +incdir+$VMM_HOME/sv+.
           +incdir+ethernet
           +incdir+$VMM_HOME/sv/examples/std_lib/wishbone
           +incdir+$VMM_HOME/sv/examples/std_lib/ethernet
           -suppress 2218 +define+SOLVER_WEIRDNESS"

VSIM_ARGS="-c -do questa.do -sv_lib $VMM_DPI_DIR/vmm_str_dpi
           -L $VMM_HOME/shared/examples/oc_ethernet/rtl/work_rtl -suppress 2218"

# ralgen not support on Windows
#$VMM_HOME/shared/bin/linux/ralgen -l sv -t oc_ethernet oc_ethernet.ralf
#$VMM_HOME/shared/bin/linux/ralgen -l sv -t dual_eth    dual_eth.ralf
cp ral_oc_ethernet_pregen.sv ral_oc_ethernet.sv
cp ral_dual_eth_pregen.sv ral_dual_eth.sv


# precompile the rtl
pushd $VMM_HOME/shared/examples/oc_ethernet/rtl
vlib work_rtl
vlog -work work_rtl -f rtl_file_list.lst +define+SINGLE_RAM_VARIABLE
popd

vlib work
vlog $VLOG_ARGS blk_trivial_test.sv | tee blk_trivial_test.log
if [ $? -eq 0 ]; then
 vsim $VSIM_ARGS blk_top test -l blk_trivial_test.log
fi

vlog $VLOG_ARGS dual_eth.v sys_trivial_test.sv | tee sys_trivial_test.log
if [ $? -eq 0 ]; then
  vsim $VSIM_ARGS sys_top -suppress 8385 test -l sys_trivial_test.log
fi


# internal use only
EX=$VMM_HOME/sv/examples
if [ -n "$INTEROP_REGRESS" ] ; then
  perl $EX/regress/regress_passfail.pl blk_trivial_test.log "subenv/oc_ethernet" $EX/results.log
  perl $EX/regress/regress_passfail.pl sys_trivial_test.log "subenv/oc_ethernet" $EX/results.log
fi
