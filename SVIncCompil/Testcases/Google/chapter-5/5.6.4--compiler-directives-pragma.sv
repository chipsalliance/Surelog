/*
:name: pragma-directive
:description: Try to set a pragma
:should_fail: 0
:tags: 5.6.4
*/

module ts();
`pragma protect
  wire protected_wire;
`pragma protect end
endmodule
