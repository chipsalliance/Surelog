// Regression: a generate-for bounded by an interface localparam read through
// the interface port (`sub.BYT`), but NESTED inside another generate block
// (`generate if (ALIGNED) begin: aligned ... end`).  When nested, the compile
// context is the gen-scope definition (which has no ports), so the interface
// port lives on the ENCLOSING module definition — resolveInterfacePortMember
// must walk up the parent-scope chain to find it.  Mirrors the jeras/rp32
// tcb_lite_lib_logsize2byteena aligned/unaligned byte-enable loops; without the
// walk the loops drop and the SoC read/write data path is undriven (X).
package p;
  typedef struct packed { int unsigned DAT; } bus_t;
  typedef struct packed { bus_t BUS; } cfg_t;
  localparam cfg_t CFG_DEF = '{BUS: '{DAT: 32}};
endpackage
interface bus_if #(parameter p::cfg_t CFG = p::CFG_DEF);
  localparam int unsigned BYT = CFG.BUS.DAT/8;    // = 4, via a struct-param field
  logic [BYT-1:0] ben;
endinterface
module child #(parameter bit ALIGNED = 1) (bus_if sub, output logic [3:0] o);
  generate
    if (ALIGNED == 1'b1) begin : aligned
      for (genvar i = 0; i < sub.BYT; i++) begin : g
        assign o[i] = sub.ben[i];
      end
    end
  endgenerate
endmodule
module top (input logic [3:0] ben_i, output logic [3:0] o);
  import p::*;
  bus_if #(CFG_DEF) sub ();
  assign sub.ben = ben_i;
  child #(.ALIGNED(1)) c (.sub(sub), .o(o));
endmodule
