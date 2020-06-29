/*
:name: nonescaped-access
:description: Escaped identifiers can be referenced by nonescaped name
:tags: 5.6.1
*/
`default_nettype none
module identifiers();

  reg \cpu3 ;
  wire reference_test;

  assign reference_test = cpu3;

endmodule
