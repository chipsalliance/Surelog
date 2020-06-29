/*
:name: begin-keywords
:description: Begin keywords check
:tags: 5.6.4
*/

`begin_keywords "1364-2001" // use IEEE Std 1364-2001 Verilog keywords
module b_kw();
  reg logic; // OK: "logic" is not a keyword in 1364-2001
endmodule
`end_keywords
