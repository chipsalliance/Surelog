module dut();

  assign {intr_classd_o,
  intr_classc_o,
  intr_classb_o,
  intr_classa_o} = irq;

endmodule
