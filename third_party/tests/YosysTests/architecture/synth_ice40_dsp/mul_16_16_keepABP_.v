(* top *)
module mul_16_16_keepABP_ #(parameter AW=16, BW=16, AREG=1, BREG=1, PREG=1) (input clk, CEA, CEB, CEP, input [AW-1:0] A, input [BW-1:0] B, (* keep *) output reg [AW+BW-1:0] P);
(* keep *) reg [AW-1:0] Ar;
(* keep *) reg [BW-1:0] Br;
generate
    if (AREG) begin
        always @(posedge clk) if (1) Ar <= A;
    end
    else
        always @* Ar <= A;
    if (BREG) begin
        always @(posedge clk) if (1) Br <= B;
    end
    else
        always @* Br <= B;
    if (PREG) begin
        always @(posedge clk) if (1) P <= Ar * Br;
    end
    else
        always @* P <= Ar * Br;
endgenerate
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd mul_16_16_keepABP_; select t:SB_MAC16 -assert-count 1; select t:SB_DFF* -assert-count 32";
endmodule
`endif

