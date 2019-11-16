module top (
  a, b
);

  input a;
  output [35:0] b;

  reg [35:0] G;
  reg F;
  reg H;
  reg I;
  reg J;

  reg [5:0] K;
  reg [9:0] L;
  reg [9:0] M;

  assign b = muxer(G, {L , H , F , M, J , I}, K, 24, 0);

  function [35:0] muxer;
    input [35:0] vector;
    input [23:0] slice;
    input [5:0] index;
    input size;
    integer size;
    input offset;
    integer offset;
    integer i;
    reg [35:0] muxed_value;
  begin
    muxed_value = vector;
    for (i = 0; i < 24; i = i+1)
      muxed_value[index * size + offset + i] = slice[i];
    muxer = muxed_value;
  end
  endfunction

endmodule
