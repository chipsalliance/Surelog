#!/bin/sh

# Optional clean arg ($1) passed to sub-run_questas.

pushd ./HAL/fifo/null;                ./run_questa.sh $1; popd
pushd ./RAL/oc_ethernet;              ./run_questa.sh $1; popd
pushd ./perf/tl_bus;                  ./run_questa.sh $1; popd
pushd ./sb/apb_bus;                   ./run_questa.sh $1; popd
pushd ./std_lib/data_macros;          ./run_questa.sh $1; popd
pushd ./std_lib/ethernet;             ./run_questa.sh $1; popd
pushd ./std_lib/log_catcher;          ./run_questa.sh $1; popd
pushd ./std_lib/mss_simple;           ./run_questa.sh $1; popd
pushd ./std_lib/record_replay;        ./run_questa.sh $1; popd
pushd ./std_lib/scenarios;            ./run_questa.sh $1; popd
pushd ./std_lib/vmm_test/run;         ./run_questa.sh $1; popd
pushd ./std_lib/wishbone;             ./run_questa.sh $1; popd
pushd ./subenv/oc_ethernet;           ./run_questa.sh $1; popd

if [ "$1" = clean ] ; then
  rm -rf *.log *.log.filtered *.wlf transcript* work
  rm -rf ../../shared/examples/oc_ethernet/rtl/work_rtl
fi

