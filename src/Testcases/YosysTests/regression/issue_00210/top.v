module top(result);
  output signed [9:0] result;

  wire signed [9:0] intermediate [0:2];

  function integer depth2Index;
    input integer depth;

    depth2Index = depth;
  endfunction

  assign intermediate[depth2Index(2)] = 0;
  assign result = intermediate[2];
endmodule
