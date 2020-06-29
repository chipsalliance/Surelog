/*
:name: 22.5.1--define_expansion_5
:description: Test
:tags: 22.5.1
:type: preprocessing
*/
`define D(x,y) initial $display("start", x , y, "end");
module top ();
`D(  ,  )
endmodule
