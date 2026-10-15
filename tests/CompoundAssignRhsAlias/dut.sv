// A COMPOUND assignment in a constant function changed its RIGHT-HAND local.
// `a += b` is folded by MUTATING the constant reduceExpr returned for the RHS,
// and reduceExpr hands back the very object stored as b's value -- so a's new
// value landed in b as well:
//     int a,b; a=1; b=2; a+=b; return b;   // returned 3, not 2
// and a constant function built on that picked the WRONG generate arm
// (chipsalliance/Surelog#4214).  `-=`, `*=` and `/=` share the alias; `*=`
// merely hides it when a==1, because 1*b writes back exactly b's own value.
//
// Every B_* localparam below must fold to 2 (the untouched b) and every A_* to
// the value the compound assignment really produced.  SELECTED pins the arm
// the issue's own shape picks: `expected`, never `wrong`.
module dut (output [31:0] y, output y_arm);

  function automatic int f_add_b();   int a,b; a=1; b=2; a+=b; return b; endfunction
  function automatic int g_add_a();   int a,b; a=1; b=2; a+=b; return a; endfunction
  function automatic int f_sub_b();   int a,b; a=3; b=2; a-=b; return b; endfunction
  function automatic int g_sub_a();   int a,b; a=3; b=2; a-=b; return a; endfunction
  function automatic int f_mul_b();   int a,b; a=3; b=2; a*=b; return b; endfunction
  function automatic int g_mul_a();   int a,b; a=3; b=2; a*=b; return a; endfunction
  function automatic int f_div_b();   int a,b; a=6; b=2; a/=b; return b; endfunction
  function automatic int g_div_a();   int a,b; a=6; b=2; a/=b; return a; endfunction
  function automatic int f_chain_b(); int a,b; a=1; b=2; a+=b; a+=b; return b; endfunction
  function automatic int g_chain_a(); int a,b; a=1; b=2; a+=b; a+=b; return a; endfunction

  localparam int B_ADD   = f_add_b();    // 2
  localparam int A_ADD   = g_add_a();    // 3
  localparam int B_SUB   = f_sub_b();    // 2
  localparam int A_SUB   = g_sub_a();    // 1
  localparam int B_MUL   = f_mul_b();    // 2
  localparam int A_MUL   = g_mul_a();    // 6
  localparam int B_DIV   = f_div_b();    // 2
  localparam int A_DIV   = g_div_a();    // 3
  localparam int B_CHAIN = f_chain_b();  // 2
  localparam int A_CHAIN = g_chain_a();  // 5

  assign y = B_ADD + A_ADD + B_SUB + A_SUB + B_MUL
           + A_MUL + B_DIV + A_DIV + B_CHAIN + A_CHAIN;   // 2+3+2+1+2+6+2+3+2+5 = 28

  // The issue's own shape: the generate arm the folded value selects.
  if (B_ADD == 2) begin : expected
    localparam int SELECTED = 1;
    assign y_arm = 1'b1;
  end else begin : wrong
    localparam int SELECTED = 0;
    assign y_arm = 1'b0;
  end
endmodule
