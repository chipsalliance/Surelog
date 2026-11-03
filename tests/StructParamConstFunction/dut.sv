package cfg_pkg;
  // the nested optional config: a pattern-valued package parameter passed
  // as the function's struct-typed argument (obi_pkg's ObiMinimalOptionalConfig)
  typedef struct packed {
    bit          UseAtop;
    int unsigned AUserWidth;
  } opt_t;
  localparam opt_t MinimalOpt = '{
    UseAtop:    1'b0,
    AUserWidth: 3
  };
  typedef struct packed {
    bit          UseRReady;
    int unsigned AddrWidth;
    int unsigned DataWidth;
    int unsigned IdWidth;
    opt_t        Opt;
  } cfg_t;
  function automatic cfg_t default_cfg(int unsigned AddrWidth, int unsigned DataWidth,
                                       int unsigned IdWidth, opt_t Opt);
    default_cfg = '{
      UseRReady: 1'b0,
      AddrWidth: AddrWidth,
      DataWidth: DataWidth,
      IdWidth:   IdWidth,
      Opt:       Opt
    };
  endfunction
  localparam cfg_t DefaultCfg = default_cfg(32, 32, 1, MinimalOpt);
endpackage

module child #(
  parameter cfg_pkg::cfg_t Cfg = cfg_pkg::DefaultCfg
) (
  input  logic [Cfg.DataWidth-1:0] d_i,
  output logic [Cfg.DataWidth-1:0] d_o,
  output logic [Cfg.Opt.AUserWidth-1:0] au_o
);
  logic [Cfg.DataWidth-1:0] rsp_data;
  always_comb begin
    rsp_data = '0;
    rsp_data = d_i;
  end
  assign d_o = rsp_data;
  assign au_o = d_i[Cfg.Opt.AUserWidth-1:0];
endmodule

module dut (
  input  logic [31:0] d_i,
  output logic [31:0] d_o,
  output logic [2:0]  au_o,
  output logic        ok_o
);
  localparam cfg_pkg::cfg_t Cfg = cfg_pkg::DefaultCfg;
  child #(.Cfg(Cfg)) u_c (.d_i(d_i), .d_o(d_o), .au_o(au_o));
  // An elaboration-time $error pins the FOLDED VALUES in the golden log
  // (the UHDM object stats alone do not see the generate arms).
  if (Cfg.DataWidth == 32 && Cfg.AddrWidth == 32 && Cfg.IdWidth == 1 &&
      Cfg.Opt.AUserWidth == 3 && !Cfg.UseRReady) begin : g_folded
    assign ok_o = d_i[0];
  end else begin : g_unfolded
    $error("DefaultCfg did not fold to {32, 32, 1, {0, 3}}");
    assign ok_o = 1'b0;
  end
endmodule
