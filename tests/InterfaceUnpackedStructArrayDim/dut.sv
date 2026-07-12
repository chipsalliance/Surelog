// Regression for interface UNPACKED struct-array dimension drop: an interface's
// `pkt_t arr [0:N]` was written into the interface DEFINITION as a bare
// element-width logic_net, losing the [0:N] dimension (only the elaborated
// instance kept it as an array_net).  The definition now also emits a
// dimensioned array_net in Array_nets(), so a reader of arr[1] sees 2 elements.
// A revert drops the def-level array_net, lowering the array_net stat below.
package p;
  typedef struct packed { logic [7:0] a; logic [7:0] b; } pkt_t;
endpackage
interface bus_if #(parameter int N = 1);
  import p::*;
  pkt_t arr [0:N];
  modport mp (input arr);
endinterface
module sub (bus_if.mp s, output logic [7:0] o);
  assign o = s.arr[1].a;
endmodule
module top (output logic [7:0] o);
  bus_if #(.N(1)) bus ();
  sub u (.s(bus.mp), .o(o));
endmodule
