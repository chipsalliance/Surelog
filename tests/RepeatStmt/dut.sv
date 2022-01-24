module GOOD ();
endmodule

module constfunc11();

function [31:0] pow2(input [5:0] x);

begin:body
  pow2 = 1;
  repeat (x) begin
    pow2 = 2 * pow2;
  end
end

endfunction

localparam val0 = pow2(4);

if (val0 == 16) begin
   GOOD good();
end

endmodule // constfunc11
