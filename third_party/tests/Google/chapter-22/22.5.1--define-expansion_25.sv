/*
:name: 22.5.1--define_expansion_25
:description: Test
:tags: 22.5.1
:type: preprocessing
*/
`define msg(x,y) `"x: `\`"y`\`"`"
module top ();
initial $display(`msg(left side,right side));
endmodule
