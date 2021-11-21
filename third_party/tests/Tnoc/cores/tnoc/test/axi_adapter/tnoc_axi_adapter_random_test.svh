`ifndef TNOC_AXI_ADAPTER_RANDOM_TEST_SVH
`define TNOC_AXI_ADAPTER_RANDOM_TEST_SVH
class tnoc_axi_adapter_random_test_sequence extends tnoc_axi_adapter_test_sequence_base;
  task body();
    foreach (p_sequencer.axi_master_sequencer[y, x]) begin
      random_test(y, x);
    end
    wait fork;
  endtask

  task random_test(int y, int x);
    for (int i = 0;i < 80;++i) begin
      fork begin
        tvip_axi_master_access_sequence axi_sequence;
        `uvm_do_on(axi_sequence, p_sequencer.axi_master_sequencer[y][x])
      end join_none
    end
  endtask

  `tue_object_default_constructor(tnoc_axi_adapter_random_test_sequence)
  `uvm_object_utils(tnoc_axi_adapter_random_test_sequence)
endclass

class tnoc_axi_adapter_random_test extends tnoc_axi_adapter_test_base;
  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    set_default_sequence(sequencer, "main_phase", tnoc_axi_adapter_random_test_sequence::type_id::get());
  endfunction
  `tue_component_default_constructor(tnoc_axi_adapter_random_test)
  `uvm_component_utils(tnoc_axi_adapter_random_test)
endclass
`endif
