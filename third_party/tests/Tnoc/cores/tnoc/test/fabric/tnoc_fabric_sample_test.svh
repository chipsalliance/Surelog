`ifndef TNOC_FABRIC_SAMPLE_TEST_SVH
`define TNOC_FABRIC_SAMPLE_TEST_SVH
class tnoc_fabric_sample_test_sequence extends tnoc_fabric_test_sequence_base;
  task body();
    for (int y = 0;y < configuration.size_y;++y) begin
      for (int x = 0;x < configuration.size_x;++x) begin
        main_process(y, x);
      end
    end
  endtask

  task main_process(int y, int x);
    for (int i = 0;i < configuration.size_y;++i) begin
      for (int j = 0;j < configuration.size_x;++j) begin
        do_noc_access(p_sequencer.bfm_sequencer[y][x], i, j);
      end
    end
  endtask

  task do_noc_access(uvm_sequencer_base sequencer, int y, int x);
    for (int i =0;i < 20;++i) begin
      tnoc_bfm_packet_item  packet_item;
      `uvm_do_on_with(packet_item, sequencer, {
        destination_id.x == x;
        destination_id.y == y;
        if ((i % 2) == 0) {
          packet_type inside {TNOC_BFM_RESPONSE, TNOC_BFM_RESPONSE_WITH_DATA};
        }
        else {
          packet_type inside {TNOC_BFM_READ, TNOC_BFM_POSTED_WRITE, TNOC_BFM_NON_POSTED_WRITE};
        }
      })
    end
  endtask

  `tue_object_default_constructor(tnoc_fabric_sample_test_sequence)
  `uvm_object_utils(tnoc_fabric_sample_test_sequence)
endclass

class tnoc_fabric_sample_test extends tnoc_fabric_test_base;
  function void start_of_simulation_phase(uvm_phase phase);
    set_default_sequence(sequencer, "main_phase", tnoc_fabric_sample_test_sequence::type_id::get());
  endfunction

  `tue_component_default_constructor(tnoc_fabric_sample_test)
  `uvm_component_utils(tnoc_fabric_sample_test)
endclass
`endif
