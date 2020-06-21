module dut;

  typedef struct packed {
     bit   [7:0]   addr;
     bit   [7:0]   data;
     bit           wr;
  } mem_s;

  mem_s mem1;
  
  mem_s mem2 [2];
  
  typedef struct {
     logic   [7:0]   addr;
     logic   [7:0]   data;
     logic           wr;
  } intf;
  
  wire intf intf1;
  
  wire intf intf2  [2];
  

endmodule // dut

module test;
  dut u1();
initial
  $vpi_decompiler(test);
endmodule
