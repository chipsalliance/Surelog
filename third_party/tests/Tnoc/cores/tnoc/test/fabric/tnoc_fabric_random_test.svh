`ifndef TNOC_FABRIC_RANDOM_TEST_SVH
`define TNOC_FABRIC_RANDOM_TEST_SVH
class tnoc_fabric_random_test_sequence extends tnoc_fabric_test_sequence_base;
  task body();
    foreach (p_sequencer.bfm_sequencer[y, x]) begin
      fork
        automatic uvm_sequencer_base  sequencer = p_sequencer.bfm_sequencer[y][x];
        do_noc_access(sequencer);
      join_none
    end
    wait fork;
  endtask

  task do_noc_access(uvm_sequencer_base sequencer);
    repeat (20) begin
      tnoc_bfm_packet_item  packet_item;
      `uvm_do_on_with(packet_item, sequencer, {
        destination_id.x inside {[0:local::configuration.size_x]};
        destination_id.y inside {[0:local::configuration.size_y]};
      })
    end
  endtask

  `tue_object_default_constructor(tnoc_fabric_random_test_sequence)
  `uvm_object_utils(tnoc_fabric_random_test_sequence)
endclass

class tnoc_fabric_random_test extends tnoc_fabric_test_base;
  function void start_of_simulation_phase(uvm_phase phase);
    set_default_sequence(sequencer, "main_phase", tnoc_fabric_random_test_sequence::type_id::get());
  endfunction

  `tue_component_default_constructor(tnoc_fabric_random_test)
  `uvm_component_utils(tnoc_fabric_random_test)
endclass
`endif
