
// Annulls a value (gates it to zero)

// We put something this simple into a module since it conveys intent,
// and avoids an RTL schematic cluttered with a bunch of AND gates.

// We do this using logic instead of a register synchronous clear
// since it might not be as portable, nor synthesize as well.

// See http://www.altera.com/literature/hb/qts/qts_qii51007.pdf (page 14-49):

// // Creating many registers with different sload and sclr signals can make
// // packing the registers into LABs difficult for the Quartus II Fitter
// // because the sclr and sload signals are LAB-wide signals. In addition,
// // using the LAB-wide sload signal prevents the Fitter from packing
// // registers using the quick feedback path in the device architecture,
// // which means that some registers cannot be packed with other logic.

// // Synthesis tools typically restrict use of sload and sclr signals to
// // cases in which there are enough registers with common signals to allow
// // good LAB packing. Using the look-up table (LUT) to implement the signals
// // is always more flexible if it is available.  Because different device
// // families offer different numbers of control signals, inference of these
// // signals is also device-specific. For example, because Stratix II devices
// // have more flexibility than Stratix devices with respect to secondary
// // control signals, synthesis tools might infer more sload and sclr signals
// // for Stratix II devices.

`default_nettype none

module Annuller
#(
    parameter       WORD_WIDTH         = 0
)
(
    input   wire                       annul,
    input   wire    [WORD_WIDTH-1:0]   in,
    output  reg     [WORD_WIDTH-1:0]   out
);

    initial begin
        out = 0;
    end

    always @(*) begin
        out <= (annul == 1'b1) ? {WORD_WIDTH{1'b0}} : in;
    end

endmodule

