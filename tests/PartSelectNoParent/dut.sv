package my_pkg;
   parameter int Shares = 2;
   parameter int KeyWidth = 256;
   parameter int NumRegsKey = 8;

   typedef struct packed {
      logic [Shares-1:0][KeyWidth-1:0] key;
   } hw_key_req_t;
endpackage // my_pkg

module top(output int o);
   import my_pkg::*;
   hw_key_req_t keymgr_key_i = '1;
   always_comb begin : key_sideload_get
      for (int i = 0; i < NumRegsKey; i++) begin
         o = keymgr_key_i.key[0][31 : 0];
      end
   end
endmodule
