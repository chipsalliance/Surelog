module dut(input logic a, input logic b, output logic y, output logic z);
  // attribute instance between the keyword and the statement (pulp_riscv_dbg dm_csrs)
  always_comb (* xprop_off *) begin : blk
    y = a & b;
  end
  always_ff (* keep *) @(posedge a) z <= b;
endmodule
