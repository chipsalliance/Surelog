module dut(var3);
  typedef struct packed {
      logic [5:0] third;
  } struct2;

  output struct2 var3 [7];

  for (genvar i=0; i<7; i++) begin : g_fill
      assign var3[i] = struct2'(127);
  end
endmodule;

