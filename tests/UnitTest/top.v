interface mem_if (input wire clk, output wire ooo);
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