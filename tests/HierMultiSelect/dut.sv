module dm_csrs ();
  assign dmi_req_i.addr1 = dmi_req_i.addr2 ;
  assign kmac_mask_o[8*i+:8] = {8{keymgr_data_i.strb[i]}};
  assign o = keymgr_key_i.key[0][1 * 32 +: 32]; // Multi select
  assign sram_otp_key_o[2-2].nonce = 1;
  logic c = a[0].source[6 -: 2];
  byte o = b.and;
endmodule
