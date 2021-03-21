../../UVM/1800.2-2017-1.0/src/uvm_pkg.sv --cc -CFLAGS "-std=c++11" snapshots/default/common_defines.vh design/include/swerv_types.sv -Idesign/include -Idesign/lib  -Isnapshots/default -Wno-UNOPTFLAT  -Itestbench -f testbench/flist testbench/tb_top.sv testbench/ahb_sif.sv --top-module tb_top -verbose -parse -elabuhdm -d coveruhdm



