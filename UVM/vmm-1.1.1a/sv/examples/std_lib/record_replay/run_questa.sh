#!/bin/sh

if [ -z "$VMM_HOME" ] ; then
VMM_HOME=../../../..
fi

if [ -z "$VMM_DPI_DIR" ] ; then
VMM_DPI_DIR=$VMM_HOME/shared/lib/linux_x86_64
fi

if [ "$1" = clean ] ; then
  rm -rf *.log *.log.filtered *.wlf transcript* work *.dat questa.do; exit
fi


echo "set SolveArrayResizeMax 5000; run -all; quit" > questa.do

VLOG_ARGS="-mfcu -sv +incdir+$VMM_HOME/sv+."
VSIM_ARGS="-c -do questa.do -sv_lib $VMM_DPI_DIR/vmm_str_dpi"

vlib work

vlog $VLOG_ARGS test.sv | tee normal.log

if [ $? -eq 0 ]; then
  vsim $VSIM_ARGS +vmm_opts+NUM_TRANS=3+NUM_CHANS=1  +vmm_MODE=NORMAL   test -l normal.log
  vsim $VSIM_ARGS +vmm_opts+NUM_TRANS=10+NUM_CHANS=2 +vmm_MODE=RECORD   test -l record.log
  vsim $VSIM_ARGS +vmm_opts+NUM_TRANS=10+NUM_CHANS=2 +vmm_MODE=PLAYBACK test -l playback.log
fi

# internal use only
EX=$VMM_HOME/sv/examples
if [ -n "$INTEROP_REGRESS" ] ; then
  perl $EX/regress/regress_passfail.pl normal.log   "std_lib/record_replay" $EX/results.log
  perl $EX/regress/regress_passfail.pl record.log   "std_lib/record_replay" $EX/results.log
  perl $EX/regress/regress_passfail.pl playback.log "std_lib/record_replay" $EX/results.log
fi

