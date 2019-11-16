# Basic synthesis file to replicate DFFSR bug

yosys -import
set libfile osu018_stdcells_edit.lib

read_verilog -sv sd_rrmux.v

# Vanilla synth flow
hierarchy
procs
fsm
opt
techmap
opt

dfflibmap -liberty $libfile

abc -liberty $libfile

clean

write_verilog sd_rrmux_osu.gv

