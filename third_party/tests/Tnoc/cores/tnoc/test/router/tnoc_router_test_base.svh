`ifndef TNOC_ROUTER_TEST_BASE_SVH
`define TNOC_ROUTER_TEST_BASE_SVH
class tnoc_router_test_base extends tnoc_test_base #(
  .CONFIGURATION  (tnoc_router_env_configuration  ),
  .ENV            (tnoc_router_env                ),
  .SEQUENCER      (tnoc_router_env_sequencer      )
);
  `tue_component_default_constructor(tnoc_router_test_base)
endclass

class tnoc_router_test_sequence_base extends tnoc_sequence_base #(
  tnoc_router_env_sequencer, tnoc_router_env_configuration
);
  `tue_object_default_constructor(tnoc_router_test_sequence_base)
endclass
`endif
