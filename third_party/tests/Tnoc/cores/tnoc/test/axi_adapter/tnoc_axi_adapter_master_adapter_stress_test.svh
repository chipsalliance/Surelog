`ifndef TNOC_AXI_ADAPTER_MASTER_ADAPTER_STRESS_TEST_SVH
`define TNOC_AXI_ADAPTER_MASTER_ADAPTER_STRESS_TEST_SVH
class tnoc_axi_adapter_master_adapter_stress_test_sequence extends tnoc_axi_adapter_test_sequence_base;
  task body();
    for (int i = 0;i < 3;++i) begin
      foreach (p_sequencer.axi_master_sequencer[y, x]) begin
        fork
          automatic int ii  = i;
          automatic int yy  = y;
          automatic int xx  = x;
          master_adapter_stress_test(ii, yy, xx);
        join_none
      end
      wait fork;
    end
  endtask

  task master_adapter_stress_test(int master_index, int y, int x);
    tvip_axi_master_sequencer sequencer;
    tvip_axi_configuration    axi_cfg;
    sequencer = p_sequencer.axi_master_sequencer[y][x];
    axi_cfg   = sequencer.get_configuration();
    for (int i = 0;i < 20;++i) begin
      tvip_axi_master_write_sequence  write_sequence;
      tvip_axi_master_read_sequence   read_sequence;
      `uvm_do_on_with(write_sequence, sequencer, {
        address[axi_cfg.address_width-2+:2] == master_index;
      })
      `uvm_do_on_with(read_sequence, sequencer, {
        address      == write_sequence.address;
        burst_size   == write_sequence.burst_size;
        burst_length == write_sequence.burst_length;
      })
    end
  endtask

  `tue_object_default_constructor(tnoc_axi_adapter_master_adapter_stress_test_sequence)
  `uvm_object_utils(tnoc_axi_adapter_master_adapter_stress_test_sequence)
endclass

class tnoc_axi_adapter_master_adapter_stress_test extends tnoc_axi_adapter_test_base;
  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    set_default_sequence(sequencer, "main_phase", tnoc_axi_adapter_master_adapter_stress_test_sequence::type_id::get());
  endfunction
  `tue_component_default_constructor(tnoc_axi_adapter_master_adapter_stress_test)
  `uvm_component_utils(tnoc_axi_adapter_master_adapter_stress_test)
endclass
`endif
