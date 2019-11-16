////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s        SystemVerilog Tutorial        s////
////s           gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////////////////////////////////////////////////
`ifndef GUARD_COVERAGE
`define GUARD_COVERAGE

class coverage;
packet pkt;

covergroup switch_coverage;

length : coverpoint pkt.length;
da     : coverpoint pkt.da {
            bins p0 = { `P0 }; 
            bins p1 = { `P1 }; 
            bins p2 = { `P2 }; 
            bins p3 = { `P3 }; } 
length_kind : coverpoint pkt.length_kind;
fcs_kind : coverpoint pkt.fcs_kind;

all_cross:  cross length,da,length_kind,fcs_kind;
endgroup

function new();
switch_coverage = new();
endfunction : new

task sample(packet pkt);
this.pkt = pkt;

switch_coverage.sample();
endtask:sample
endclass

`endif
