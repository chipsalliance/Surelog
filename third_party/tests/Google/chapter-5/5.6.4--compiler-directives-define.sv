/*
:name: define-directive
:description: Define and undef checks
:tags: 5.6.4
*/

`define XXX 1

`ifdef XXX
`undef XXX
`elsif YYY 
`define XXX 0
`endif

`ifndef YYY
`define YYY 0
`else
`define XXX 0
`endif

`undefineall

module d();
endmodule
