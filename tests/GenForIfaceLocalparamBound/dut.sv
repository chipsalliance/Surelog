// Regression: a generate-for whose loop bound is an INTERFACE LOCALPARAM read
// through the interface instance/port (`sub.BYT`), from a module that takes the
// interface as a port.  The interface instance isn't bound to the port yet at
// generate-elaboration time, so Surelog previously could not fold the bound and
// silently dropped the whole loop (0 gen scopes).  Mirrors the jeras/rp32
// tcb_lite_lib_logsize2byteena byte-enable / read-data reshaping loops
// (`for (i=0; i<sub.CFG_BUS_BYT; i++)`), whose absence left the fetch/read data
// path undriven (X).
interface bus_if #(parameter int DAT = 32);
  localparam int unsigned BYT = DAT/8;          // interface localparam (=4)
  logic [BYT-1:0] ben;
endinterface

module child (bus_if sub, output logic [3:0] o);
  generate
    for (genvar i = 0; i < sub.BYT; i++) begin : g
      assign o[i] = sub.ben[i];
    end
  endgenerate
endmodule

module top (input logic [3:0] ben_i, output logic [3:0] o);
  bus_if #(.DAT(32)) sub ();
  assign sub.ben = ben_i;
  child c (.sub(sub), .o(o));
endmodule
