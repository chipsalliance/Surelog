`ifndef TNOC_COMMON_ENV_PKG_SV
`define TNOC_COMMON_ENV_PKG_SV
package tnoc_common_env_pkg;
  import  uvm_pkg::*;
  import  tue_pkg::*;
  import  tnoc_bfm_types_pkg::*;
  import  tnoc_bfm_pkg::*;

  `include  "uvm_macros.svh"
  `include  "tue_macros.svh"

  `uvm_analysis_imp_decl(_tx)
  `uvm_analysis_imp_decl(_rx)

  `include  "tnoc_common_utilities.svh"
  `include  "tnoc_packet_scoreboard.svh"
  `include  "tnoc_model_base.svh"
  `include  "tnoc_sequence_base.svh"
  `include  "tnoc_test_base.svh"
endpackage
`endif
