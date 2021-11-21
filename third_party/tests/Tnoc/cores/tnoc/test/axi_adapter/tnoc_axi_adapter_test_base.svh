`ifndef TNOC_AXI_ADAPTER_TEST_BASE_SVH
`define TNOC_AXI_ADAPTER_TEST_BASE_SVH
class tnoc_axi_adapter_test_base extends tnoc_test_base #(
  .CONFIGURATION  (tnoc_axi_adapter_env_configuration ),
  .ENV            (tnoc_axi_adapter_env               ),
  .SEQUENCER      (tnoc_axi_adapter_env_sequencer     )
);
  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    foreach (env.axi_slave_agent[i, j]) begin
      set_default_sequence(
        env.axi_slave_agent[i][j].sequencer,
        "run_phase",
        tvip_axi_slave_default_sequence::type_id::get()
      );
    end
  endfunction

  `tue_component_default_constructor(tnoc_fabric_test_base)
endclass

class tnoc_axi_adapter_test_sequence_base extends tnoc_sequence_base #(
  tnoc_axi_adapter_env_sequencer, tnoc_axi_adapter_env_configuration
);
  `tue_object_default_constructor(tnoc_axi_adapter_test_sequence_base)
endclass
`endif
