// Simple adder/subtractor module
module ADD_SUB(
  input            clk,
  input [7:0]      a0,
  input [7:0]      b0,
  // if this is 1, add; else subtract
  input            doAdd0,
  output reg [8:0] result0
);

  always @ (posedge clk)
    begin
      if (doAdd0)
        result0 <= a0 + b0;
      else
        result0 <= a0 - b0;
    end

endmodule: ADD_SUB

//---------------------------------------
// Interface for the adder/subtractor DUT
//---------------------------------------
interface add_sub_if(
  input bit clk,
  input [7:0] a,
  input [7:0] b,
  input       doAdd,
  input [8:0] result
);

  clocking cb @(posedge clk);
    output    a;
    output    b;
    output    doAdd;
    input     result;
  endclocking // cb

endinterface: add_sub_if

//---------------
// Interface bind
//---------------
bind ADD_SUB add_sub_if add_sub_if0(
  .clk(clk),
  .a(a0),
  .b(b0),
  .doAdd(doAdd0),
  .result(result0)
);
