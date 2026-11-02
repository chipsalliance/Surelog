// A compound assignment used as an EXPRESSION: `b = (a -= 1)` must subtract.
// The expression alternative of the grammar lists the assignment tokens inline,
// and nothing recorded which one was written, so the compiler emitted a plain
// assignment and `b = (a -= 1)` meant `b = (a = 1)`.  The expression form now
// carries the operator as `operation(vpiAssignmentOp, [a, operation(<op>, [a, rhs])])`;
// the statement form (line `a -= 1;`) keeps the operator on the assignment node.
module top(input int x, input int y, output int a_o, b_o, c_o, d_o);
  always_comb begin
    int a, b, c, d;
    a = x;
    a -= 1;                       // statement form: 11 (vpiSubOp) on the assignment
    b = (a -= 1);                 // expression form, subtract
    c = (a += 2);                 // expression form, add
    d = ((b += (a += 1) + 1));    // nested: both updates visible
    a_o = a; b_o = b; c_o = c; d_o = d;
  end
endmodule
