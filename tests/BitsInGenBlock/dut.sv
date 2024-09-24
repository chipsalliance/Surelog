module GOOD();

endmodule; // GOOD

module ibex_top  (
 
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  output byte b
);



generate
  if (1) begin
   
    localparam int NumBufferBits = $bits({
  
      instr_req_o, // 1 bit
      instr_gnt_i, // 1 bit
      b // 8 bits
    });

  if (NumBufferBits == 10) begin
     GOOD good();
  end
     
end
endgenerate

endmodule
