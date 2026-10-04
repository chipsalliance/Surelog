// A constant function that stages values in a LOCAL UNPACKED ARRAY and
// combines the elements: ExprEval stored the array as its element vector,
// one bit per index, so `st[0] ^ st[1]` folded to 1 instead of
// 58'h300_0000_0000_0001 (verilog-ethernet lfsr_mask).  Every output below
// must fold to 64'h0300000000000001.
module dut (output [63:0] y_direct, output [63:0] y_loop, output [63:0] y_while);
  function [63:0] f_direct(input [31:0] dummy);
    reg [57:0] st [0:1];
    begin
      st[0] = 58'h200_0000_0000_0001;
      st[1] = 58'h100_0000_0000_0000;
      f_direct = st[0] ^ st[1];
    end
  endfunction
  function [63:0] f_loop(input [31:0] dummy);
    reg [57:0] st [0:1];
    integer k;
    begin
      st[0] = 58'h200_0000_0000_0001;
      st[1] = 58'h100_0000_0000_0000;
      f_loop = 0;
      for (k = 0; k < 2; k = k + 1) f_loop = f_loop ^ st[k];
    end
  endfunction
  function [63:0] f_while(input [31:0] dummy);
    reg [57:0] st [0:1];
    integer k;
    begin
      st[0] = 58'h200_0000_0000_0001;
      st[1] = 58'h100_0000_0000_0000;
      f_while = 0; k = 0;
      while (k < 2) begin f_while = f_while ^ st[k]; k = k + 1; end
    end
  endfunction
  assign y_direct = f_direct(0);
  assign y_loop   = f_loop(0);
  assign y_while  = f_while(0);
endmodule
