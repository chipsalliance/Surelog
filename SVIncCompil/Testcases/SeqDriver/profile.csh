LD_PRELOAD=/usr/lib/libprofiler.so.0 CPUPROFILE=./surelog.prof ../../dist/Debug/GNU-Linux/surelog -timescale=1ns/1ns +vcs+flush+all +warn=all -sverilog    -d 0 +incdir+.+../../../UVM/uvm-1.2/src/  -write_pp   -verbose  -mt max -parse -fileunit design.sv testbench.sv
google-pprof --web ../../dist/Debug/GNU-Linux/surelog surelog.prof
