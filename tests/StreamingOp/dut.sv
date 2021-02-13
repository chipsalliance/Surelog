module dut;
  assign z = { << 4 {x, y} };
  assign y = { << {32'd123456, x} };
  assign conv_data = { >> 8 {v}}; 
endmodule
