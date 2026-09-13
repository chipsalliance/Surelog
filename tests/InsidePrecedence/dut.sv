// `expr inside {..}` binds at the relational level (IEEE 1800-2017 Table
// 11-2), above the conditional operator: a chained
//   a inside {R1} ? x : a inside {R2} ? y : z
// must parse as (a inside R1) ? x : ((a inside R2) ? y : z) — it used to parse
// as ((a inside R1) ? x : a) inside R2 ? y : z (OpenTitan reg_top steering).
module dut(input logic [31:0] a, output logic [1:0] s, output logic u);
  localparam int AW = 12;
  always_comb begin
    s = a[AW-1:0] inside {[1024:1535]} ? 2'd0 :
        a[AW-1:0] inside {[2048:4095]} ? 2'd1 :
        2'd2;
    u = a inside {32'd5, [32'd100:32'd200]} && a[0];
  end
endmodule
