`ifndef TNOC_ROUTER_TESTS_PKG_SV
`define TNOC_ROUTER_TESTS_PKG_SV
package tnoc_router_tests_pkg;
  import  uvm_pkg::*;
  import  tue_pkg::*;
  import  tnoc_bfm_types_pkg::*;
  import  tnoc_bfm_pkg::*;
  import  tnoc_common_env_pkg::*;
  import  tnoc_router_env_pkg::*;

  `include  "uvm_macros.svh"
  `include  "tue_macros.svh"

  `include  "tnoc_router_test_base.svh"
  `include  "tnoc_router_sample_test.svh"
  `include  "tnoc_router_different_route_test.svh"
  `include  "tnoc_router_output_arbitration_test.svh"
  `include  "tnoc_router_virtual_channel_test.svh"
  `include  "tnoc_router_invalid_destination_test.svh"
  `include  "tnoc_router_stress_access_test.svh"
  `include  "tnoc_router_random_test.svh"
endpackage
`endif

