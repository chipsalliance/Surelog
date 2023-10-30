package keymgr_pkg;
   parameter int Shares = 2;
   parameter int KeyWidth = 16;

   typedef struct packed {
      logic [Shares-1:0][KeyWidth-1:0] key;
   } hw_key_req_t;

typedef struct  {
   logic [31:0] pair[2];
} foo_t;


endpackage // keymgr_pkg

module GOOD();
endmodule

module top(output int o);
   keymgr_pkg::hw_key_req_t keymgr_key_i;
    keymgr_pkg::foo_t a;
  
  parameter p1 = $bits(keymgr_key_i.key[0]);
  parameter p2 = $bits(a.pair[0]);

  if (p1 == 16) begin
     GOOD p1u();
  end

  if (p2 == 32) begin
    GOOD p2u();
  end

 // initial $display("o1: %d, o2:  %d", o1, o2);
  
endmodule // top