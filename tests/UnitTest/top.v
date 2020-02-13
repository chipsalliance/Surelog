

module top (input i, output o);
wire i;
reg o;
assign o = i;
endmodule


interface mem_if (input wire clk);

  modport  system (input clk);
  modport  memory (output clk);
 
endinterface

class DD2;
endclass

module memory_ctrl1 (mem_if sif1, mem_if.system sif2);

DD1 toto1;

DD2 toto2;

wire i1;

reg o1;

endmodule

