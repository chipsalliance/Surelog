module top( input logic [31:0] instr_rdata_i);

 always_comb begin : csr_pipeline_flushes
  
    if (int'(instr_rdata_i[31:20]) == CSR_MSTATUS) begin
        csr_pipe_flush = 1'b1;
      end
 end

endmodule

