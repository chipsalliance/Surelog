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

module prim_generic_ram_1 ();

  typedef enum logic [1:0] {
    PMP_MODE_TOR   = 2'b01
  } pmp_cfg_mode_e;
  typedef struct packed {
    logic          lock;
    pmp_cfg_mode_e mode;
  } pmp_cfg_t;

  pmp_cfg_t     pmp_cfg  [2];
  
 for (genvar i = 0; i < 2; i++) begin : g_pmp_csrs

  assign pmp_addr_we = ~pmp_cfg[i].lock &
  (pmp_cfg[i+1].mode != PMP_MODE_TOR);

 end

endmodule


module test;
  dut u1();
  prim_generic_ram_1 u2();
  
initial
  $vpi_decompiler(test);
endmodule
