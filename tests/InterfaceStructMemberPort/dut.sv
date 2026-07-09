// Interface modport struct MEMBER as a child instance port ACTUAL.
// `.sys_wdt(sub.req.wdt)` (plain member) and `.sys_wen(sub.req.wen & sub.trn)`
// (member inside an expression) must keep the member selection: high_conn_ must
// NOT reduce the member access to the whole `req` struct_net.  Each inner port's
// High_conn should be a hier_path/operation carrying the member, not a bare
// struct_net.  Regression for the interface-member port-connection fix.
package p;
  typedef struct packed { logic [31:0] wdt; logic wen; } req_t;
endpackage

interface tif;
  p::req_t req;
  logic    trn;
  modport sub (input req, input trn);
endinterface

module inner (input logic [31:0] sys_wdt, input logic sys_wen,
              output logic [31:0] o);
  assign o = sys_wen ? sys_wdt : '0;
endmodule

module wrapper (tif.sub sub, output logic [31:0] o);
  inner u (.sys_wdt(sub.req.wdt), .sys_wen(sub.req.wen & sub.trn), .o(o));
endmodule

module top (input logic [31:0] din, input logic en, input logic t,
            output logic [31:0] o);
  tif s();
  assign s.req.wdt = din;
  assign s.req.wen = en;
  assign s.trn     = t;
  wrapper w (.sub(s.sub), .o(o));
endmodule
