`ifndef TNOC_ROUTER_ENV_PKG_SV
`define TNOC_ROUTER_ENV_PKG_SV
package tnoc_router_env_pkg;
  import  uvm_pkg::*;
  import  tue_pkg::*;
  import  tnoc_bfm_types_pkg::*;
  import  tnoc_bfm_pkg::*;
  import  tnoc_common_env_pkg::*;

  `include  "uvm_macros.svh"
  `include  "tue_macros.svh"

  `include  "tnoc_router_env_configuration.svh"
  `include  "tnoc_router_env_model.sv"
  `include  "tnoc_router_env_sequencer.svh"
  `include  "tnoc_router_env.svh"
endpackage
`endif
