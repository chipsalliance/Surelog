`ifndef TNOC_AXI_ADAPTER_TESTS_PKG_SV
`define TNOC_AXI_ADAPTER_TESTS_PKG_SV
package tnoc_axi_adapter_tests_pkg;
  import  uvm_pkg::*;
  import  tue_pkg::*;
  import  tvip_axi_types_pkg::*;
  import  tvip_axi_pkg::*;
  import  tnoc_common_env_pkg::*;
  import  tnoc_axi_adapter_env_pkg::*;

  `include  "uvm_macros.svh"
  `include  "tue_macros.svh"

  `include  "tnoc_axi_adapter_test_base.svh"
  `include  "tnoc_axi_adapter_sample_test.svh"
  `include  "tnoc_axi_adapter_slave_adapter_stress_test.svh"
  `include  "tnoc_axi_adapter_master_adapter_stress_test.svh"
  `include  "tnoc_axi_adapter_random_test.svh"
endpackage
`endif
