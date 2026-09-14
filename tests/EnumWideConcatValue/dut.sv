package pwc_pkg;
  parameter logic [31:0] A = 32'hF00D_BEEF, B = 32'h1234_5678, C = 32'hDEAD_C0DE, D = 32'h0BAD_F00D;
  typedef enum logic [127:0] {
    Cnt0 = {A, B, C, D},
    Cnt1 = {B, C, D, A},
    Cnt2 = {C, D, A, B},
    Cnt3 = {D, A, B, C}
  } cnt_e;
endpackage
module dut import pwc_pkg::*; (input cnt_e c_i, input logic inc_i, output cnt_e n_o, output logic oflw_o);
  always_comb begin
    n_o = c_i; oflw_o = 1'b0;
    if (inc_i) begin
      unique case (c_i)
        Cnt0: n_o = Cnt1;
        Cnt1: n_o = Cnt2;
        Cnt2: n_o = Cnt3;
        Cnt3: oflw_o = 1'b1;
        default: oflw_o = 1'b1;
      endcase
    end
  end
endmodule
