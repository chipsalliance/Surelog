// Check inference even when not in vector
(* top *)
module test17a (input clk, input i, output q);
generate 
    reg a1, a2, a3, a4, a5, a6, a7, a8;
    always @(posedge clk) a1 <= i;
    always @(posedge clk) a2 <= a1;
    always @(posedge clk) a3 <= a2;
    always @(posedge clk) a4 <= a3;
    always @(posedge clk) a5 <= a4;
    always @(posedge clk) a6 <= a5;
    always @(posedge clk) a7 <= a6;
    always @(posedge clk) a8 <= a7;
    assign q = a8;
endgenerate
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd test17a; select t:SRL16E -assert-count 1; select t:BUFG t:SRL16E %% %n t:* %i -assert-none";
endmodule
`endif
