#!/bin/sh

if [ "$1" = clean ] ; then
  rm -rf *.log *.log.filtered *.wlf transcript* work questa.do ral_oc_ethernet.sv; exit
fi

if [ -z "$1" ] ; then
LIST="hw_reset bit_bash reg_access mem_walk"
else
LIST=$1
fi

if [ -z "$VMM_HOME" ] ; then
${VMM_HOME:=../../../..}
fi

if [ -z "$VMM_DPI_DIR" ] ; then
${VMM_DPI_DIR:=$VMM_HOME/shared/lib/linux_x86_64}
fi


#internal use only
check () {
  if [ -n "$INTEROP_REGRESS" ] ; then
    perl $VMM_HOME/sv/examples/regress/regress_passfail.pl $EXAMPLE.log "RAL/oc_ethernet" $VMM_HOME/sv/examples/results.log
  fi
}

#----------------------------------------------------------------------

echo "set SolveArrayResizeMax 5000; run -all; quit" > questa.do

VLOG_ARGS="-mfcu -sv +define+OC_ETHERNET_BUG +incdir+$VMM_HOME/sv+.
           timescale.v 
           -L $VMM_HOME/shared/examples/oc_ethernet/rtl/work_rtl 
           +incdir+$VMM_HOME/sv/examples/std_lib/ethernet
           +incdir+$VMM_HOME/sv/examples/std_lib/wishbone
           +define+OC_ETHERNET_TOP_PATH=tb_top.dut
           +define+SINGLE_RAM_VARIABLE -suppress 2218 -suppress 2240
           +define+VMM_RAL_TEST_PRE_INCLUDE=ral_env.svh
           +define+VMM_RAL_TEST_POST_INCLUDE=ral_pgm.svh"

VSIM_ARGS="-c -do questa.do -sv_lib $VMM_DPI_DIR/vmm_str_dpi
           -L $VMM_HOME/shared/examples/oc_ethernet/rtl/work_rtl -suppress 2218 tb_top"

# ralgen not supported on all questa platforms
#$VMM_HOME/shared/bin/linux/ralgen -l sv -t oc_ethernet $VMM_HOME/shared/examples/oc_ethernet/oc_ethernet.ralf
cp ral_oc_ethernet_pregen.sv ral_oc_ethernet.sv

pushd $VMM_HOME/shared/examples/oc_ethernet/rtl
vlib work_rtl
vlog -work work_rtl -f rtl_file_list.lst +define+SINGLE_RAM_VARIABLE
popd

EX=$VMM_HOME/sv/examples

vlib work

for EXAMPLE in $LIST; do

  vlog $VLOG_ARGS $VMM_HOME/sv/RAL/tests/$EXAMPLE.sv tb_top.sv | tee $EXAMPLE.log
  if [ $? -eq 0 ]; then
    vsim $VSIM_ARGS $EXAMPLE -l $EXAMPLE.log
  fi

  check

done
