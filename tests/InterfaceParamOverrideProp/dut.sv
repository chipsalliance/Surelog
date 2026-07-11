// Regression for the getInterfaceInstance_ modport-actual bug: an interface
// parameter OVERRIDE must propagate onto the interface-port copies created when
// the interface is passed down through module ports via a modport (`.t(inst.mp)`).
package p;
  typedef struct { int unsigned DLY; } hsk_t;
  typedef struct { hsk_t HSK; } cfg_t;
  localparam cfg_t CFG_DEF = '{HSK: '{DLY: 1}};
endpackage
interface tif #(parameter p::cfg_t CFG = p::CFG_DEF);
  logic [7:0] sig;
  modport mp (input sig);
endinterface
module leaf (tif.mp t, output logic [7:0] o);
  assign o = t.sig;              // pass-through only; the CFG override is what matters
endmodule
module mid (tif.mp t, output logic [7:0] o);
  leaf u (.t(t), .o(o));
endmodule
module top (output logic [7:0] o);
  localparam p::cfg_t CFG_OVR = '{HSK: '{DLY: 0}};
  tif #(CFG_OVR) inst ();        // DLY override 0 must reach the port copies
  mid u (.t(inst.mp), .o(o));
endmodule
