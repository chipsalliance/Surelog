
import uvm_pkg::* ;
`include "uvm_macros.svh"

interface mem_if2 (input clk);
  wire clk;
  logic        reset;
  
  modport  system (input clk, reset);
 
  modport  tb (input clk, output reset, toto);


 generate
for(genvar i = 0; i < 2; i++) begin : mod_gen
  modport  tb (clocking cb, input clk);
end
endgenerate

endinterface

module toto (a, output b, c);
    wire a,b,c;
endmodule


module toto1 (ab, f, output b, c);
    wire a,b,c;
endmodule


//+++++++++++++++++++++++++++++++++++++++++++++++++
// Define the interface
//+++++++++++++++++++++++++++++++++++++++++++++++++
interface mem_if (input wire clk);
  wire        reset;
  wire        we;
  wire        ce;
  wire  [7:0] datai;
  logic [7:0] datao;
  wire  [7:0] addr;
  //=================================================
  // Clocking block for testbench
  //=================================================
  clocking cb @ (posedge clk);
    output reset, we, ce, datai,addr;
    input  datao;
  endclocking
  //=================================================
  // Modport for testbench 
  //=================================================
  modport  tb (clocking cb, input clk);

endinterface

//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With interface
//+++++++++++++++++++++++++++++++++++++++++++++++++
module simple_if (mem_if mif);
// Memory array
logic [7:0] mem [0:255];

//=================================================
// Read logic
//=================================================
always @ (posedge mif.clk)
 if (mif.reset) mif.datao <= 0;
 else if (mif.ce && !mif.we) mif.datao <= mem[mif.addr];

//=================================================
// Write Logic
//=================================================
always @ (posedge mif.clk)
 if (mif.ce && mif.we) mem[mif.addr] <= mif.datai;

endmodule

//+++++++++++++++++++++++++++++++++++++++++++++++++
//  Testbench
//+++++++++++++++++++++++++++++++++++++++++++++++++
module tb();

logic clk = 0;
always #10 clk++;
//=================================================
// Instianciate Interface and DUT 
//=================================================
mem_if miff(clk);
simple_if U_dut(miff);
//=================================================
// Default clocking  
//=================================================
default clocking dclk @ (posedge clk);

endclocking
//=================================================
// Test Vector generation
//=================================================
initial begin
  miff.tb.cb.reset <= 1;
  miff.tb.cb.ce <= 1'b0;
  miff.tb.cb.we <= 1'b0;
  miff.tb.cb.addr <= 0;
  miff.tb.cb.datai <= 0;
  ##1 miff.tb.cb.reset <= 0;
  for (int i = 0; i < 3; i ++ ) begin
    ##1 miff.tb.cb.ce <= 1'b1;
    miff.tb.cb.we <= 1'b1;
    miff.tb.cb.addr <= i;
    miff.tb.cb.datai <= $random;
    ##3 miff.tb.cb.ce <= 1'b0;
    $display ("@%0dns Write access address %x, data %x",
      $time,miff.addr,miff.datai);
  end
  for (int i = 0; i < 3; i ++ ) begin
    ##1 miff.tb.cb.ce <= 1'b1;
    miff.tb.cb.we <= 1'b0;
    miff.tb.cb.addr <= i;
    ##3 miff.tb.cb.ce <= 1'b0;
    $display ("@%0dns Read access address %x, data %x",
      $time,miff.addr,miff.datao);
  end
  #10 $finish;
end

endmodule
