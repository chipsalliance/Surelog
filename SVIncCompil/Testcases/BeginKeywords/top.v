/*
`begin_keywords "1364-2001" 
module b_kw1();
  reg logic; // OK: "logic" is not a keyword in 1364-2001
endmodule
`end_keywords
*/
module b_kw2();
logic clk;
endmodule
/*
module b_kw3();
  reg logic; // BAD: "logic" is a keyword in 1800-2017
endmodule
*/