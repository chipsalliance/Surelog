(* top *)
module multien_var_len (input clk, en1, en2, i, input [2:0] l, output q);
reg [6:0] r;
always @(posedge clk) begin
    if (en1) begin
        r[2:0] <= {r[1:0], i};
        r[6:4] <= r[5:3];
    end
    if (en2)
        r[3] <= r[2];
end
assign q = r[l];
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd multien_var_len; select t:SRL* -assert-count 0; select t:FD* -assert-count 7";
endmodule
`endif
