/*
:name: 22.5.1--define_expansion_7
:description: Test
:should_fail: 1
:tags: 22.5.1
:type: preprocessing
*/
`define D(x,y) initial $display("start", x , y, "end");
`D()
