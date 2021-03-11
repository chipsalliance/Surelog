module dut();
function automatic logic [7:0] aes_rev_order_bit(logic [7:0] in);
  logic [7:0] out;
  for (int i=0; i<8; i++) begin
    out[i] = in[7-i];
  end
  return out;
endfunction

logic [7:0]       ctr_we_o_rev, ctr_we_o;

assign ctr_we_o_rev = 8'b00001111;

assign ctr_we_o = aes_rev_order_bit(ctr_we_o_rev);
endmodule
