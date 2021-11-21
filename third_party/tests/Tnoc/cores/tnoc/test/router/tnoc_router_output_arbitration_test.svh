`ifndef TNOC_ROUTER_OUTPUT_ARBITRATION_TEST_SEQUENCE_SVH
`define TNOC_ROUTER_OUTPUT_ARBITRATION_TEST_SEQUENCE_SVH
class tnoc_router_output_arbitration_test_sequence extends tnoc_router_test_sequence_base;
  tnoc_bfm_location_id  destinations[2];

  task body();
    setup();
    for (int i = 0;i < 2;++i) begin
      fork
        do_noc_access(p_sequencer.bfm_sequencer[0], i);
        do_noc_access(p_sequencer.bfm_sequencer[1], i);
        do_noc_access(p_sequencer.bfm_sequencer[2], i);
        do_noc_access(p_sequencer.bfm_sequencer[3], i);
        do_noc_access(p_sequencer.bfm_sequencer[4], i);
      join
    end
  endtask

  function void setup();
    tnoc_bfm_location_id  port_list[5]  = '{
      get_location_id(1, 2), get_location_id(1, 0),
      get_location_id(2, 1), get_location_id(0, 1),
      get_location_id(1, 1)
    };
    port_list.shuffle();
    destinations[0] = port_list[0];
    destinations[1] = port_list[1];
  endfunction

  task do_noc_access(uvm_sequencer_base sequencer, int index);
    for (int i = 0;i < 10;++i) begin
      tnoc_bfm_packet_item  packet_item;
      `uvm_do_on_with(packet_item, sequencer, {
        if (index == 0) {
          packet_type inside {TNOC_BFM_RESPONSE, TNOC_BFM_RESPONSE_WITH_DATA};
          destination_id == destinations[0];
        }
        else {
          packet_type inside {TNOC_BFM_READ, TNOC_BFM_POSTED_WRITE, TNOC_BFM_NON_POSTED_WRITE};
          destination_id == destinations[1];
        }

      })
    end
  endtask

  `tue_object_default_constructor(tnoc_router_output_arbitration_test_sequence)
  `uvm_object_utils(tnoc_router_output_arbitration_test_sequence)
endclass

class tnoc_router_output_arbitration_test extends tnoc_router_test_base;
  function void start_of_simulation_phase(uvm_phase phase);
    set_default_sequence(sequencer, "main_phase", tnoc_router_output_arbitration_test_sequence::type_id::get());
  endfunction

  `tue_component_default_constructor(tnoc_router_output_arbitration_test)
  `uvm_component_utils(tnoc_router_output_arbitration_test)
endclass
`endif
