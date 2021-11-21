`ifndef TNOC_FABRIC_TEST_BASE_SVH
`define TNOC_FABRIC_TEST_BASE_SVH
class tnoc_fabric_test_base extends tnoc_test_base #(
  .CONFIGURATION  (tnoc_fabric_env_configuration  ),
  .ENV            (tnoc_fabric_env                ),
  .SEQUENCER      (tnoc_fabric_env_sequencer      )
);
  `tue_component_default_constructor(tnoc_fabric_test_base)
endclass

class tnoc_fabric_test_sequence_base extends tnoc_sequence_base #(
  tnoc_fabric_env_sequencer, tnoc_fabric_env_configuration
);
  `tue_object_default_constructor (tnoc_fabric_test_sequence_base)
endclass
`endif
