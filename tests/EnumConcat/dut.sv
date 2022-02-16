
module GOOD();
endmodule


module dut ();
typedef enum logic [5:0] {
  EXC_CAUSE_IRQ_SOFTWARE_M     = {1'b1, 5'd03}
} exc_cause_e;

  if (EXC_CAUSE_IRQ_SOFTWARE_M == 6'b100011) begin
    GOOD good();
  end

endmodule
