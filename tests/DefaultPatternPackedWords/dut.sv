// `'{default: v}` over a MULTI-RANGE packed logic parameter fills each WORD
// element with v (iDMA's `logic [NumDim-1:0][31:0] RepWidths = '{default:
// RepWidth}`), not every bit; a single range keeps the per-bit fill.
module dut #(
  parameter int unsigned NumDim   = 32'd3,
  parameter int unsigned RepWidth = 32'd16
) (
  input  logic        a,
  output logic [95:0] words_o,
  output logic [95:0] lit_o,
  output logic [7:0]  bits_o,
  output logic [31:0] w1_o
);
  localparam logic [NumDim-1:0][31:0] RepWidths = '{default: RepWidth};
  localparam logic [2:0][31:0]        Literal   = '{default: 32'd16};
  localparam logic [7:0]              Bits      = '{default: 1'b1};
  assign words_o = RepWidths;
  assign lit_o   = Literal;
  assign bits_o  = Bits;
  assign w1_o    = RepWidths[1];
  // An elaboration-time $error pins the FOLDED VALUES in the golden log (the
  // UHDM object stats alone do not see generate arms): the per-bit fill made
  // every word 32'hFFFF_FFFF.
  if (RepWidths[1] == 32'd16 && RepWidths[0] == 32'd16 && Literal[2] == 32'd16 &&
      Bits == 8'hFF) begin : g_folded
  end else begin : g_unfolded
    $error("'{default: v} over logic [N:0][31:0] did not fill per word");
  end
endmodule
