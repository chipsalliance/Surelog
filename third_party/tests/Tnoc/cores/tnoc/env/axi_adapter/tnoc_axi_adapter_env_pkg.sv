`ifndef TNOC_AXI_ADAPTER_ENV_PKG_SV
`define TNOC_AXI_ADAPTER_ENV_PKG_SV
package tnoc_axi_adapter_env_pkg;
  import  uvm_pkg::*;
  import  tue_pkg::*;
  import  tvip_axi_types_pkg::*;
  import  tvip_axi_pkg::*;
  import  tnoc_bfm_types_pkg::*;
  import  tnoc_bfm_pkg::*;
  import  tnoc_common_env_pkg::*;
  import  tnoc_fabric_env_pkg::*;

  `include  "uvm_macros.svh"
  `include  "tue_macros.svh"

  `include  "tnoc_axi_adapter_env_configuration.svh"
  `include  "tnoc_axi_adapter_env_sequencer.svh"
  `include  "tnoc_axi_adapter_env.svh"
endpackage
`endif
