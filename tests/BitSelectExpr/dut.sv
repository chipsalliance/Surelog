module top(output int o);

   typedef struct packed {
      int 	  nonce;
   } sram_otp_key_rsp_t;
   
   sram_otp_key_rsp_t [2:0] sram_otp_key_o;

   assign sram_otp_key_o[2-2].nonce = 1;


endmodule // top

