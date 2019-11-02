#!/bin/sh

if [ "$1" = clean ] ; then
  rm -rf *.log *.log.filtered *.wlf transcript* work data.out questa.do; exit
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
    perl $VMM_HOME/sv/examples/regress/regress_passfail.pl $EXAMPLE.log "std_lib/ethernet" $VMM_HOME/sv/examples/results.log
  fi
}

#----------------------------------------------------------------------

if [ -z "$1" ] ; then
LIST="test_frame test_mac test_mii"
else
LIST=$1
fi

echo "set SolveArrayResizeMax 5000; run -all; quit" > questa.do

VLOG_ARGS="-mfcu -sv +define+OC_ETHERNET_BUG +incdir+$VMM_HOME/sv+."
VSIM_ARGS="-c -do questa.do -sv_lib $VMM_DPI_DIR/vmm_str_dpi"

vlib work

for EXAMPLE in $LIST; do

  if [ "$EXAMPLE" = "test_frame" ] ; then
    vlog $VLOG_ARGS test_frame.sv | tee $EXAMPLE.log
    if [ $? -eq 0 ]; then
	  vsim $VSIM_ARGS test_frame -l $EXAMPLE.log
	fi
  else
    vlog $VLOG_ARGS $EXAMPLE.sv top.sv | tee $EXAMPLE.log
    if [ $? -eq 0 ]; then
      vsim $VSIM_ARGS top p mii_mac_bfm -l $EXAMPLE.log
	fi
  fi

  check

done

