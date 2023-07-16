package axi_pkg;
  typedef struct packed {
    int unsigned   NoSlvPorts;
    int unsigned   NoMstPorts;
    int unsigned   AxiAddrWidth;
  } xbar_cfg_t;
endpackage

module axi_xbar
#(
  parameter axi_pkg::xbar_cfg_t Cfg                                   = '0,
  parameter DEBUG = Cfg.NoSlvPorts,
  parameter bit [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] Connectivity = '1
) (
);  
endmodule

package cheshire_pkg;
  localparam axi_pkg::xbar_cfg_t AxiXbarCfg = '{
    NoSlvPorts:         5,
    NoMstPorts:         5,
    AxiAddrWidth:       48
  };
endpackage

module cheshire_soc import cheshire_pkg::*; #() ();
  axi_xbar #(
    .Cfg            ( AxiXbarCfg                    )
  ) i_axi_xbar ();
endmodule
