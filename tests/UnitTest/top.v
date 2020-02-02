module dff0_test(n1);
  (* init = 32'd1 *)
  output n1;
  reg n1 = 32'd0;
endmodule

/*
interface AXI_BUS #(
 parameter AXI_ID_WIDTH   = -1
);

  typedef logic [AXI_ID_WIDTH-1:0]   id_t;
  
  id_t1       aw_id;
   
  modport Master (
    output aw_id
  );

  id_t       rw_id;
   
  modport Slave (
    output ww_id
  );

endinterface


interface mem_if (input wire clk);

  modport  system (input clk);
  modport  memory (input clk);
 
endinterface

module memory_ctrl1 (mem_if.system1 sif);

typedef  enum {IDLE,WRITE,READ,DONE} fsm_t;

fsm_t state;


endmodule

module memory_ctrl2 (mem_if.system sif);

typedef  enum {IDLE,WRITE,READ,DONE} fsm_t;

fsm_t state;

DD t;

endmodule

*/
