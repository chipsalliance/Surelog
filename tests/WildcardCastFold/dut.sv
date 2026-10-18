// A size cast of a literal with ? / x / z digits must keep them: these are
// address MATCH patterns (black-parrot's cfg_mem_cce_ucode_match_gp), and the
// numeric fold turned `(20)'('h0_8???)` into UINT:8.
package p;
  localparam dev_w = 20;
  localparam [dev_w-1:0] UCODE  = (dev_w)'('h0_8???);
  localparam [dev_w-1:0] LOWER  = (dev_w)'('b????_??1?_????);
  localparam [dev_w-1:0] XFILL  = (dev_w)'('hx_x);
  localparam [dev_w-1:0] PLAIN  = (dev_w)'('h0_8000);
  localparam [7:0]       HEXQ   = 8'h?;
  localparam [7:0]       HEXLO  = 8'hab;
endpackage
module top import p::*; (input logic [19:0] a, input logic [7:0] b, output logic y1, y2, y3, y4, y5, y6);
  assign y1 = a inside {UCODE};
  assign y2 = a inside {LOWER};
  assign y3 = a inside {XFILL};
  assign y4 = a == PLAIN;
  assign y5 = b inside {HEXQ};
  assign y6 = b == HEXLO;
endmodule
