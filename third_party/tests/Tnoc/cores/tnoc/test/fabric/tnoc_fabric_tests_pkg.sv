`ifndef TNOC_FABRIC_TESTS_PKG_SV
`define TNOC_FABRIC_TESTS_PKG_SV
package tnoc_fabric_tests_pkg;
  import  uvm_pkg::*;
  import  tue_pkg::*;
  import  tnoc_bfm_types_pkg::*;
  import  tnoc_bfm_pkg::*;
  import  tnoc_common_env_pkg::*;
  import  tnoc_fabric_env_pkg::*;

  `include  "uvm_macros.svh"
  `include  "tue_macros.svh"

  `include  "tnoc_fabric_test_base.svh"
  `include  "tnoc_fabric_sample_test.svh"
  `include  "tnoc_fabric_invalid_destination_test.svh"
  `include  "tnoc_fabric_stress_access_test.svh"
  `include  "tnoc_fabric_random_test.svh"
endpackage
`endif

