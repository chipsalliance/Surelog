`ifndef TNOC_ROUTER_SAMPLE_TEST_SVH
`define TNOC_ROUTER_SAMPLE_TEST_SVH
class tnoc_router_sample_test_sequence extends tnoc_router_test_sequence_base;
  task body();
    main_process(0);
    main_process(1);
    main_process(2);
    main_process(3);
    main_process(4);
  endtask

  task main_process(int port);
    do_noc_access(port, 2, 1);
    do_noc_access(port, 0, 1);
    do_noc_access(port, 1, 2);
    do_noc_access(port, 1, 0);
    do_noc_access(port, 1, 1);
  endtask

  task do_noc_access(int port, int x, int y);
    for (int i =0;i < 20;++i) begin
      tnoc_bfm_packet_item  packet_item;
      `uvm_do_on_with(packet_item, p_sequencer.bfm_sequencer[port], {
        destination_id.x == x;
        destination_id.y == y;
        if (i < 10) {
          packet_type inside {TNOC_BFM_RESPONSE, TNOC_BFM_RESPONSE_WITH_DATA};
        }
        else {
          packet_type inside {TNOC_BFM_READ, TNOC_BFM_POSTED_WRITE, TNOC_BFM_NON_POSTED_WRITE};
        }
      })
    end
  endtask

  `tue_object_default_constructor(tnoc_router_sample_test_sequence)
  `uvm_object_utils(tnoc_router_sample_test_sequence)
endclass

class tnoc_router_sample_test extends tnoc_router_test_base;
  function void start_of_simulation_phase(uvm_phase phase);
    set_default_sequence(sequencer, "main_phase", tnoc_router_sample_test_sequence::type_id::get());
  endfunction

  `tue_component_default_constructor(tnoc_router_sample_test)
  `uvm_component_utils(tnoc_router_sample_test)
endclass
`endif
