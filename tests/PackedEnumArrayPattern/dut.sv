// A packed array of ENUMS as a parameter, initialised by an assignment
// pattern, element-selected in generate conditions (fpnew's FmtUnitTypes).
//
// Before the fix: the tagged '{default:} never reached a packed_array_typespec
// (every element stayed 0 = DISABLED), a positional pattern sized each operand
// to the WHOLE array, and the value was materialised as one enum_var PER BIT
// -- so no `P[i] == PARALLEL` generate condition could be evaluated and no
// generate arm was elaborated.
package fp_pkg;
  typedef enum logic [1:0] { DISABLED, PARALLEL, MERGED } unit_type_t;
  localparam int unsigned NUM_FMT = 3;
  typedef unit_type_t [0:NUM_FMT-1] fmt_unit_types_t;   // ascending
  typedef unit_type_t [NUM_FMT-1:0] fmt_unit_types_d_t; // descending
endpackage

module dut #(
  parameter fp_pkg::fmt_unit_types_t   Def  = '{default: fp_pkg::PARALLEL},
  parameter fp_pkg::fmt_unit_types_t   Idx  = '{default: fp_pkg::PARALLEL, 1: fp_pkg::MERGED},
  parameter fp_pkg::fmt_unit_types_t   Pos  = '{fp_pkg::PARALLEL, fp_pkg::DISABLED, fp_pkg::MERGED},
  parameter fp_pkg::fmt_unit_types_d_t Desc = '{default: fp_pkg::DISABLED, 2: fp_pkg::PARALLEL}
) (
  input  logic [fp_pkg::NUM_FMT-1:0] in_i,
  output logic [fp_pkg::NUM_FMT-1:0] def_o, idx_o, pos_o, desc_o
);
  for (genvar fmt = 0; fmt < int'(fp_pkg::NUM_FMT); fmt++) begin : gen_fmt
    if (Def[fmt] == fp_pkg::PARALLEL) begin : def_par
      assign def_o[fmt] = in_i[fmt];
    end else begin : def_other
      assign def_o[fmt] = 1'b0;
    end
    if (Idx[fmt] == fp_pkg::MERGED) begin : idx_mrg
      assign idx_o[fmt] = ~in_i[fmt];
    end else if (Idx[fmt] == fp_pkg::PARALLEL) begin : idx_par
      assign idx_o[fmt] = in_i[fmt];
    end else begin : idx_other
      assign idx_o[fmt] = 1'b0;
    end
    if (Pos[fmt] == fp_pkg::PARALLEL) begin : pos_par
      assign pos_o[fmt] = in_i[fmt];
    end else if (Pos[fmt] == fp_pkg::MERGED) begin : pos_mrg
      assign pos_o[fmt] = ~in_i[fmt];
    end else begin : pos_dis
      assign pos_o[fmt] = 1'b0;
    end
    if (Desc[fmt] == fp_pkg::PARALLEL) begin : desc_par
      assign desc_o[fmt] = in_i[fmt];
    end else begin : desc_other
      assign desc_o[fmt] = 1'b0;
    end
  end
endmodule
