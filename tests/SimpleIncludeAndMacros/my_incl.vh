// my_incl.vh
// If we have not included file before,
// this symbol _my_incl_vh_ is not defined.
`ifndef _my_incl_vh_
`define _my_incl_vh_
`line 200 "fake.sv" 0
// Start of include contents

// Use parentheses to mitigate any undesired operator precedence issues
`define M (`N << 2)

`define INCLUSION_FILES \
  `include "mode.vh"

`define xyz(I,R = DEFAULT) \
assign abc[I].clk = R.du``I``_clk_x;


`define single 30

`define MACRO1(a=5,b="B",c) $display(a,,b,,c); 

`define msg(x,y) `"x: `\`"y`\`"`"

`define WB_DUT_U_ASSIGN(phy_i,idx)\
assign b[phy_i] = `DUT_PATH.Ilane``idx``.a;\
 
`define DUT_PATH $root

`endif //_my_incl_vh_

