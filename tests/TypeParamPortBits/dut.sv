// `$bits` of a signal declared over a TYPE PARAMETER, evaluated in a
// module-level localparam.  The type is bound by the parent, so the width is
// only known per instance: cheshire's apb_uart_wrap writes
//   localparam obi_cfg_t ObiCfg = obi_default_cfg($bits(apb_req_i.paddr), ...)
// and the call stayed an unfolded assignment pattern with its formals
// unbound, so every struct member written over `ObiCfg.*` measured one bit.
package cfg_pkg;
  typedef struct packed {
    int unsigned AddrWidth;
    int unsigned DataWidth;
  } cfg_t;
  function automatic cfg_t default_cfg(int unsigned AddrWidth,
                                       int unsigned DataWidth);
    default_cfg = '{AddrWidth: AddrWidth, DataWidth: DataWidth};
  endfunction
endpackage

module wrap #(
  parameter type apb_req_t = logic
) (
  input  apb_req_t    apb_req_i,
  input  logic [31:0] d_i,
  output logic [31:0] d_o,
  output logic        ok_o
);
  localparam int W_MEMBER = $bits(apb_req_i.paddr);   // selected primary
  localparam int W_PORT   = $bits(apb_req_i);         // whole port
  localparam int W_TYPE   = $bits(apb_req_t);         // the type itself
  localparam int W_DEP    = W_MEMBER + 1;
  localparam cfg_pkg::cfg_t Cfg =
      cfg_pkg::default_cfg($bits(apb_req_i.paddr), 32);
  typedef struct packed {
    logic [Cfg.AddrWidth-1:0] addr;
    logic [Cfg.DataWidth-1:0] wdata;
  } req_t;
  req_t r;
  assign r = '{addr: apb_req_i.paddr, wdata: d_i};
  assign d_o = r.wdata ^ {27'd0, r.addr};
  // An elaboration-time $error pins the FOLDED VALUES in the golden log.
  if (W_MEMBER == 5 && W_PORT == 6 && W_TYPE == 6 && W_DEP == 6 &&
      Cfg.AddrWidth == 5 && Cfg.DataWidth == 32 && $bits(req_t) == 37)
  begin : g_folded
    assign ok_o = d_i[0];
  end else begin : g_unfolded
    $error("$bits over the type-parameter port did not fold to 5/6/6/6, 5/32, 37");
    assign ok_o = 1'b0;
  end
endmodule

module dut (
  input  logic [4:0]  a_i,
  input  logic [31:0] d_i,
  output logic [31:0] d_o,
  output logic        ok_o
);
  typedef struct packed {
    logic [4:0] paddr;
    logic       psel;
  } apb_req_t;
  apb_req_t apb_req;
  assign apb_req = '{paddr: a_i, psel: 1'b1};
  wrap #(.apb_req_t(apb_req_t)) u (.apb_req_i(apb_req), .d_i, .d_o, .ok_o);
endmodule
