// An instance array whose SIZE form `[N]` is an expression: every array
// below must elaborate FOUR elements.  The size form's parse node is the
// constant_expression itself; evaluating its first CHILD read only the
// first operand (`[2*2]` -> 2 elements).
interface I; logic v; endinterface
module child(input logic a, output logic y); assign y = a; endmodule
module dut #(parameter int P = 2)(input logic a, output logic y);
  localparam int CH = 2;
  I a1[CH*2]();
  I a2[CH+2]();
  I a3[2*2]();
  I a4[2*P]();
  I a5[CH*CH]();
  I a6[4]();
  I a7[CH]();
  child c1[2*CH](.a(a), .y());
  child c2[3:0](.a(a), .y());
  assign y = a;
endmodule
