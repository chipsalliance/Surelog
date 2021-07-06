module prim_subreg_arb #(
  parameter int DW       = 32  ,
  parameter     SWACCESS = "RW"
) (
  input [DW-1:0] q
);

  if ((SWACCESS == "RW") || (SWACCESS == "WO")) begin : gen_w
    logic [DW-1:0] unused_q_wo;
    assign unused_q_wo = q;
  end else if (SWACCESS == "RO") begin : gen_ro
    logic [DW-1:0] unused_q_ro;
    assign unused_q_ro  = q;
  end
endmodule

module dut ();

 prim_subreg_arb #(
  .DW(32),
  .SWACCESS("RO")
 ) m1();
endmodule // dut
