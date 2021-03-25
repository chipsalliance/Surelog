

package pack1;


  parameter int TxWidth = 4;
 
  typedef enum logic [TxWidth-1:0] {
      On  = 4'b1010,
      Off = 4'b0101
    } lc_tx_e;
  
    typedef lc_tx_e lc_tx_t;
  
   parameter lc_tx_t LC_TX_DEFAULT = Off;

endpackage


module dut1 #(
  parameter int NrDevices = 1
  )();

  localparam int unsigned NumBitsDeviceSel = NrDevices > 1 ? $clog2(NrDevices) : 1;
  logic [NumBitsDeviceSel-1:0] device_sel_req;
  int device = 2;
  always_comb begin
    device_sel_req = NumBitsDeviceSel'(device);
  end

endmodule // dut



module dut2 #(parameter num_out_p="inv")
   (
     input [$clog2(num_out_p)-1:0] i
     ,output logic [num_out_p-1:0] o
   );
   
     if (num_out_p == 1) begin
       // suppress unused signal warning
       wire unused = i;
       assign o = 1'b1;
   end
   else begin
       assign o = (num_out_p) ' (1'b1 << i);
     end
 
endmodule



module dut3  #(parameter int unsigned       LfsrDw       = 3) ();

  bsg_dff_reset #(.width_p(2)) a1();

  bsg_dff_reset a2();
  
  assign next_lfsr_state = LfsrDw'(entropy_i) ^ ({LfsrDw{lfsr_q[0]}} & coeffs) ^ (lfsr_q >> 1);

 assign lockup = ~(|lfsr_q);

endmodule


module bsg_dff_reset  #(width_p=-1, reset_val_p=0, harden_p=0)
   (
    );


   always @(posedge clk_i)
     begin
        if (reset_i)
          data_r <= (width_p) ' (reset_val_p);
        else
          data_r <= data_i;
     end

endmodule

module dut5();
   parameter inputs_p = -1;
  parameter lg_inputs_p   = $clog2(inputs_p);
  parameter width_p = -1;
  parameter int TxWidth = 4;
    typedef enum logic [TxWidth-1:0] {
      On  = 4'b1010,
      Off = 4'b0101
    } lc_tx_e;
  
    typedef lc_tx_e lc_tx_t;
  
   parameter lc_tx_t LC_TX_DEFAULT = Off;

   wire [width_p-1:0] shifted = width_p ' ({fill, t[j]} >> (1 << j));
   if (GEN) begin
   
  always_comb
   begin
    unique casez({last_r, reqs_i})
    2'b?_0: begin sel_one_hot_n = 1'b0; tag_o = (lg_inputs_p) ' (0); end // X
    2'b0_1: begin sel_one_hot_n= 1'b1; tag_o = (lg_inputs_p) ' (0); end
      default: begin sel_one_hot_n= {1{1'bx}}; tag_o = (lg_inputs_p) ' (0); end // X 
    endcase
 end 
   end 
endmodule

