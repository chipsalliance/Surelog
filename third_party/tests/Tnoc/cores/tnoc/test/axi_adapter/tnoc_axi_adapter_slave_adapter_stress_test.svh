`ifndef TNOC_AXI_ADAPTER_SLAVE_ADAPTER_STRESS_TEST_SVH
`define TNOC_AXI_ADAPTER_SLAVE_ADAPTER_STRESS_TEST_SVH
class tnoc_axi_adapter_slave_adapter_stress_test_sequence extends tnoc_axi_adapter_test_sequence_base;
  task body();
    foreach (p_sequencer.axi_master_sequencer[i, j]) begin
      slave_adapter_stress_test(i, j);
    end
  endtask

  task slave_adapter_stress_test(int y, int x);
    tvip_axi_master_sequencer sequencer;
    sequencer = p_sequencer.axi_master_sequencer[y][x];
    for (int i = 0;i < 30;++i) begin
      fork begin
        tvip_axi_master_write_sequence  write_sequence;
        tvip_axi_master_read_sequence   read_sequence;
        `uvm_do_on(write_sequence, sequencer)
        `uvm_do_on_with(read_sequence, sequencer, {
          address      == write_sequence.address;
          burst_size   == write_sequence.burst_size;
          burst_length == write_sequence.burst_length;
        })
      end join_none
    end
    wait fork;
  endtask

  `tue_object_default_constructor(tnoc_axi_adapter_slave_adapter_stress_test_sequence)
  `uvm_object_utils(tnoc_axi_adapter_slave_adapter_stress_test_sequence)
endclass

class tnoc_axi_adapter_slave_adapter_stress_test extends tnoc_axi_adapter_test_base;
  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    set_default_sequence(sequencer, "main_phase", tnoc_axi_adapter_slave_adapter_stress_test_sequence::type_id::get());
  endfunction
  `tue_component_default_constructor(tnoc_axi_adapter_slave_adapter_stress_test)
  `uvm_component_utils(tnoc_axi_adapter_slave_adapter_stress_test)
endclass
`endif
