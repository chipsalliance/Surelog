// generate-if condition reading a 4-level interface-param struct field
// `sub.CFG.HSK.DLY` — the jeras/rp32 demultiplexer rsp_sel / register modules.
package p;
  typedef struct packed { int unsigned DLY; } hsk_t;
  typedef struct packed { hsk_t HSK; } cfg_t;
  localparam cfg_t CFG_DEF = '{HSK: '{DLY: 1}};
endpackage
interface bus_if #(parameter p::cfg_t CFG = p::CFG_DEF);
  logic clk, rst, trn;
  logic [3:0] sel;
  logic [3:0] rsp_sel;
endinterface
module child (bus_if sub);
  generate
    if (sub.CFG.HSK.DLY == 0) begin
      assign sub.rsp_sel = sub.sel;
    end else if (sub.CFG.HSK.DLY == 1) begin
      always_ff @(posedge sub.clk or posedge sub.rst)
        if (sub.rst) sub.rsp_sel <= '0;
        else if (sub.trn) sub.rsp_sel <= sub.sel;
    end
  endgenerate
endmodule
module top (input logic clk, input logic rst, input logic trn, input logic [3:0] sel, output logic [3:0] o);
  import p::*;
  bus_if #(CFG_DEF) sub ();
  assign sub.clk = clk; assign sub.rst = rst; assign sub.trn = trn; assign sub.sel = sel;
  assign o = sub.rsp_sel;
  child c (.sub(sub));
endmodule
