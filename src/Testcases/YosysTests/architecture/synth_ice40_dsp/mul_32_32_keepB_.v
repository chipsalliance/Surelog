(* top *)
module mul_32_32_keepB_ #(parameter AW=32, BW=32, AREG=1, BREG=1, PREG=0) (input clk, CEA, CEB, CEP, input [AW-1:0] A, input [BW-1:0] B, output reg [AW+BW-1:0] P);
reg [AW-1:0] Ar;
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
    wire [4095:0] assert_area = "cd mul_32_32_keepB_; select t:SB_MAC16 -assert-count 4; select t:SB_DFF* -assert-count 32";
endmodule
`endif

