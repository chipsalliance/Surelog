(* top *)
module mul_25s_18s_keepABP_ #(parameter AW=25, BW=18, AREG=1, BREG=1, PREG=1) (input clk, CEA, CEB, CEP, input signed [AW-1:0] A, input signed [BW-1:0] B, (* keep *) output reg signed [AW+BW-1:0] P);
(* keep *) reg signed [AW-1:0] Ar;
(* keep *) reg signed [BW-1:0] Br;
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
    wire [4095:0] assert_area = "cd mul_25s_18s_keepABP_; select t:DSP48E1 -assert-count 1; select t:FD* -assert-count 43";
endmodule
`endif

