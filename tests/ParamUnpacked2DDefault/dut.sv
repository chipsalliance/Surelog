// A 2-D UNPACKED parameter array whose default is a `'{default: v}` pattern.
// The default was expanded over the OUTERMOST dimension only, so each row held
// the bare element value, `IdMap[i][j]` selected nothing and the const function
// reading it never folded -- `IdTable` stayed at its all-zero seed.
module dut #(
  parameter int unsigned IdWidth    = 4,
  parameter int unsigned NumUniq    = 4,
  parameter int unsigned BaseOffset = 4,
  parameter int unsigned MapEntries = 2,
  parameter int unsigned IdMap [MapEntries-1:0][0:1] = '{default: {32'b0, 32'b0}}
) (
  input  logic [IdWidth-1:0] id_i,
  output logic [3:0]         sel_o
);
  typedef logic [3:0]            ent_t;
  typedef ent_t [2**IdWidth-1:0] map_t;

  function automatic map_t build_map();
    map_t ret = '0;
    for (int unsigned i = 0; i < 2**IdWidth; ++i)
      ret[i] = (i + BaseOffset) % NumUniq;
    for (int unsigned i = 0; i < MapEntries; ++i)
      ret[IdMap[i][0]] = IdMap[i][1];
    return ret;
  endfunction

  localparam map_t IdTable = build_map();

  assign sel_o = IdTable[id_i];
endmodule
