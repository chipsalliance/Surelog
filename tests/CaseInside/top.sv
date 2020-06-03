package dm;
  
  // debug registers
  typedef enum logic [7:0] {
    DMControl    = 8'h10,
    Data0        = 8'h11,
    Data1        = 8'h12
  } dm_csr_e;

endpackage : dm

module dm_csrs ();
  always_comb begin : csr_read_write
 
      unique case ({1'b0, dmi_req_i.addr}) inside
        
        [(dm::Data0):(dm::Data1)]: begin
         
          resp_queue_data = 1'b0;
         
        end
        
        dm::DMControl:    resp_queue_data = dmcontrol_q;
        
        default:;
      endcase
  
  end
endmodule : dm_csrs
