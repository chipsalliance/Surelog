

interface mem_if (input wire clk);

  modport  system (input clk);
  modport  memory (output clk);
 
endinterface


module memory_ctrl1 (mem_if sif1, mem_if.system sif2);

DD toto;

endmodule

