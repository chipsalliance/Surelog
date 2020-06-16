module dut;
  typedef struct packed {
     bit   [7:0]   addr;
     bit   [7:0]   data;
     bit           wr;
  } mem_s;

  mem_s mem;
endmodule // dut

