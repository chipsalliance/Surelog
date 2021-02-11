package keymgr_pkg;

  parameter int KmacDataIfWidth = 64;  // KMAC interface data width
  
  typedef struct packed {
    logic valid;
    logic [KmacDataIfWidth-1:0] data;
    logic [KmacDataIfWidth/8-1:0] strb;
    // last indicates the last beat of the data. strb can be partial only with
    // last.
    logic last;
  } kmac_data_req_t;
  
endpackage   

module top( input  keymgr_pkg::kmac_data_req_t keymgr_data_i,
 output logic [MsgWidth-1:0] kmac_mask_o  );
   
  always_comb begin
    unique case (mux_sel)
      SelKeyMgr: begin      
        for (int i = 0 ; i < $bits(keymgr_data_i.strb) ; i++) begin
          kmac_mask_o[8*i+:8] = {8{keymgr_data_i.strb[i]}};
        end
      end
    endcase
  end
endmodule // top

