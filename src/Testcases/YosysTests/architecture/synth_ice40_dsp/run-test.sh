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

wget https://raw.githubusercontent.com/YosysHQ/yosys-bench/master/verilog/benchmarks_small/mul/common.py -O common_mul.py -o /dev/null
cp ~/yosys/yosys-bench/verilog/benchmarks_small/mul/common.py common_mul.py
PYTHONPATH=".:$PYTHONPATH" python3 ../generate_mul.py
python3 ../assert_area.py
cp ../*.v .
${MAKE:-make} -f ../../../../tools/autotest.mk $seed *.v EXTRA_FLAGS="\
    -p 'design -copy-to __test __test; \
        synth_ice40 -dsp; \
        design -copy-from __test *; \
        select -assert-any __test; \
        script -scriptwire __test/w:assert_area'\
    -l ../../../../../techlibs/ice40/cells_sim.v"
