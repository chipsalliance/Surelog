#!/bin/sh

if [ -z "$1" ] ; then
LIST="test_add test_ls test_mul test_rs test_sub"
else
LIST=$1
fi

if [ "$1" = clean ] ; then
  rm -rf *.log *.log.filtered *.wlf transcript* work questa.do; exit
fi

if [ -z "$VMM_HOME" ] ; then
${VMM_HOME:=../../../../..}
fi

if [ -z "$VMM_DPI_DIR" ] ; then
${VMM_DPI_DIR:=$VMM_HOME/shared/lib/linux_x86_64}
fi

# internal use only
EX=$VMM_HOME/sv/examples
check () {
  if [ -n "$INTEROP_REGRESS" ] ; then
    perl $EX/regress/regress_passfail.pl $EXAMPLE.log "std_lib/vmm_test/run" $EX/results.log
  fi
}

#-------------------------------------------------------------------------


echo "set SolveArrayResizeMax 5000; run -all; quit" > questa.do

VLOG_ARGS="-mfcu -sv +incdir+$VMM_HOME/sv+.
           +incdir+../verif+../tests
           ../rtl/alu.v ../verif/alu_test.sv ../verif/alu_tb_top.sv"

VSIM_ARGS="-c -do questa.do -sv_lib $VMM_DPI_DIR/vmm_str_dpi alu_tb_top"

vlib work

vlog $VLOG_ARGS | tee test_add.log

for EXAMPLE in $LIST; do

  vsim $VSIM_ARGS +vmm_test=$EXAMPLE -l $EXAMPLE.log
  check

done

