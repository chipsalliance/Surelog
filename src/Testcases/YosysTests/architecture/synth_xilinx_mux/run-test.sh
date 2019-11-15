#!/bin/bash
set -e

OPTIND=1
seed=""    # default to no seed specified
while getopts "S:" opt
do
    case "$opt" in
	S) arg="${OPTARG#"${OPTARG%%[![:space:]]*}"}" # remove leading space
	   seed="SEED=$arg" ;;
    esac
done
shift "$((OPTIND-1))"

# check for Icarus Verilog
if ! which iverilog > /dev/null ; then
  echo "$0: Error: Icarus Verilog 'iverilog' not found."
  exit 1
fi

wget https://raw.githubusercontent.com/YosysHQ/yosys-bench/master/verilog/benchmarks_small/mux/generate.py -O generate_small.py -o /dev/null
wget https://raw.githubusercontent.com/YosysHQ/yosys-bench/master/verilog/benchmarks_small/mux/common.py -O common.py -o /dev/null
wget https://raw.githubusercontent.com/YosysHQ/yosys-bench/master/verilog/benchmarks_large/mux/generate.py -O generate_large.py -o /dev/null
python3 generate_small.py
python3 generate_large.py
python3 ../assert_area.py
${MAKE:-make} -f ../../../../tools/autotest.mk $seed *.v EXTRA_FLAGS="\
    -p 'design -copy-to __test __test; \
        synth_xilinx -abc9 -widemux 4; \
        design -copy-from __test *; \
        select -assert-any __test; \
        script -scriptwire __test/w:assert_area'\
    -l ../../../../../techlibs/xilinx/cells_sim.v"

# Spot tests for -widemux thresholds
set +e
../../../../../yosys -qp "synth_xilinx -widemux 1" 2> /dev/null
if [ $? -eq 0 ]; then
    echo "Expected error"
    exit 1
fi
set -e

../../../../../yosys -qp "synth_xilinx -widemux 5; select -assert-none t:MUXF*" mux_if_bal_2_1.v
../../../../../yosys -qp "synth_xilinx -widemux 4; select -assert-none t:MUXF*" mux_if_bal_2_1.v
../../../../../yosys -qp "synth_xilinx -widemux 3; select -assert-none t:MUXF*" mux_if_bal_2_1.v
../../../../../yosys -qp "synth_xilinx -widemux 2; select -assert-count 1 t:MUXF7" mux_if_bal_2_1.v

../../../../../yosys -qp "synth_xilinx -widemux 5; select -assert-none t:MUXF*" mux_case_3_3.v
../../../../../yosys -qp "synth_xilinx -widemux 4; select -assert-none t:MUXF*" mux_case_3_3.v
../../../../../yosys -qp "synth_xilinx -widemux 3; select -assert-count 6 t:MUXF*" mux_case_3_3.v
../../../../../yosys -qp "synth_xilinx -widemux 2; select -assert-count 6 t:MUXF*" mux_case_3_3.v

../../../../../yosys -qp "synth_xilinx -nowidelut -widemux 9; select -assert-none t:MUXF*" mux_index_7_5.v
../../../../../yosys -qp "synth_xilinx -nowidelut -widemux 8; select -assert-none t:MUXF*" mux_index_7_5.v
../../../../../yosys -qp "synth_xilinx -nowidelut -widemux 7; select -assert-count 15 t:MUXF*" mux_index_7_5.v
../../../../../yosys -qp "synth_xilinx -nowidelut -widemux 6; select -assert-count 15 t:MUXF*" mux_index_7_5.v

../../../../../yosys -qp "synth_xilinx -nowidelut -widemux 18; select -assert-none t:MUXF*" mux_if_unbal_16_8.v
../../../../../yosys -qp "synth_xilinx -nowidelut -widemux 17; select -assert-none t:MUXF*" mux_if_unbal_16_8.v
../../../../../yosys -qp "synth_xilinx -nowidelut -widemux 16; select -assert-count 24 t:MUXF*" mux_if_unbal_16_8.v
../../../../../yosys -qp "synth_xilinx -nowidelut -widemux 15; select -assert-count 24 t:MUXF*" mux_if_unbal_16_8.v
