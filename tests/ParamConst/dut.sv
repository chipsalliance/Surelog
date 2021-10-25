package lc_ctrl_state_pkg;
  parameter logic [1:0] B0 = 2'b01;
  parameter logic [1:0] B1 = 2'b10;
  typedef enum logic [3:0] {
    LcStScrap         = {B1,  B0}
  } lc_state_e;
endpackage

module generic_flop #(parameter logic [3:0] ResetValue = 0) ( );
endmodule

module prim_flop #( parameter logic [3:0] ResetValue = 0) ();
    generic_flop #(
      .ResetValue(ResetValue)
    ) impl_generic ();
endmodule

module top();
  import lc_ctrl_state_pkg::*;

  prim_flop #(
    .ResetValue(4'(LcStScrap))
  ) state_regs ();

endmodule

