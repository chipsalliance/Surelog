package keymgr_pkg;

 parameter int KeyWidth = 256;

 typedef struct packed {
    logic ready;
    logic done;
    logic [KeyWidth-10:0] digest_share0;
    
  } kmac_data_rsp_t;
endpackage

module OK();
endmodule
   
module kmac_keymgr(output keymgr_pkg::kmac_data_rsp_t keymgr_data_o);

 localparam int KeyMgrDigestW = $bits(keymgr_data_o.digest_share0);
 if (KeyMgrDigestW == 247)
   OK ok();
  
 logic [KeyMgrDigestW-1:0] keymgr_digest [2];

endmodule
