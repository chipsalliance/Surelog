/*
:name: desc_test_16
:description: Test
:type: preprocessing
:tags: 5.6.4
*/
`ifdef ASIC
module module_asic;
endmodule
`elsif FPGA  // ASIC
module module_fpga;
endmodule
`endif  // ASIC
