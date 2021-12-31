package keymgr_pkg;
   parameter int Shares = 2;
   parameter int KeyWidth = 16;

   typedef struct packed {
      logic [Shares-1:0][KeyWidth-1:0] key;
   } hw_key_req_t;
endpackage // keymgr_pkg

module top(output int o);
   keymgr_pkg::hw_key_req_t keymgr_key_i;
   parameter PP =  $bits(keymgr_key_i.key[0]);
   assign o = $bits(keymgr_key_i.key[0]);
endmodule // top
