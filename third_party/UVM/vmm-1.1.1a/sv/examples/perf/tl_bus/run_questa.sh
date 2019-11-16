#!/bin/sh

if [ -z "$VMM_HOME" ] ; then
VMM_HOME=../../../..
fi

if [ -z "$VMM_DPI_DIR" ] ; then
VMM_DPI_DIR=$VMM_HOME/shared/lib/linux_x86_64
fi

if [ "$1" = clean ] ; then
  rm -rf *.log *.log.filtered *.wlf transcript* work sql_data.* questa.do; exit
fi


LD_LIBRARY_PATH=$VMM_DPI_DIR:$LD_LIBRARY_PATH
export LD_LIBRARY_PATH

echo "set SolveArrayResizeMax 5000; run -all; quit" > questa.do

VLOG_ARGS="-mfcu -sv +define+OC_ETHERNET_BUG +incdir+$VMM_HOME/sv+."
VSIM_ARGS="-c -do questa.do -sv_lib $VMM_DPI_DIR/vmm_str_dpi"

vlib work

vlog $VLOG_ARGS +define+USE_SQLTXT test.sv | tee sqltxt.log
if [ $? -eq 0 ]; then
  vsim $VSIM_ARGS -sv_lib $VMM_DPI_DIR/vmm_sqltxt test -l sqltxt.log
fi

vlog $VLOG_ARGS +define+USE_SQLITE test.sv | tee sqlite.log
if [ $? -eq 0 ]; then
  vsim $VSIM_ARGS -sv_lib $VMM_DPI_DIR/vmm_sqlite test -l sqlite.log
fi


# internal use only
EX=$VMM_HOME/sv/examples
if [ -n "$INTEROP_REGRESS" ] ; then
  perl $EX/regress/regress_passfail.pl sqltxt.log "perf/tl_bus" $EX/results.log
  perl $EX/regress/regress_passfail.pl sqlite.log "perf/tl_bus" $EX/results.log
fi
