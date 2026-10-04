// A non-ANSI function (its ports are tf_item_declarations) declaring an
// unpacked local array: `tbl` must be an array_var with four 64-bit entries,
// not a 64-bit logic_var.
module dut (output [63:0] y);
  function [63:0] f0;
    input [31:0] dummy;
    reg [63:0] tbl [0:3];
    integer i;
    begin
      tbl[0] = 64'h8000_0000_0000_0001; tbl[1] = 64'h0000_0001_0000_0000;
      tbl[2] = 64'h4000_0000_0000_0000; tbl[3] = 64'h0000_0000_8000_0000;
      f0 = 0;
      for (i = 0; i < 4; i = i + 1) f0 = f0 ^ tbl[i];
    end
  endfunction
  assign y = f0(0);
endmodule
