`ifndef TNOC_ROUTER_RANDOM_TEST_SEQUENCE_SVH
`define TNOC_ROUTER_RANDOM_TEST_SEQUENCE_SVH
class tnoc_router_random_test_sequence extends tnoc_router_test_sequence_base;
  task body();
    fork
      do_noc_access(0);
      do_noc_access(1);
      do_noc_access(2);
      do_noc_access(3);
      do_noc_access(4);
    join
  endtask

  task do_noc_access(int index);
    repeat (20) begin
      tnoc_bfm_packet_item  packet_item;
      `uvm_do_on_with(packet_item, p_sequencer.bfm_sequencer[index], {
        if ((source_id.x == 1) && (source_id.y != 1)) {
          destination_id.x == 1;
          destination_id.y inside {[0:2]};
        }
        if ((source_id.x == 2) && (source_id.y == 1)) {
          destination_id.x < 2;
          destination_id.y inside {[0:2]};
        }
        if ((source_id.x == 0) && (source_id.y == 1)) {
          destination_id.x inside {[1:2]};
          destination_id.y inside {[0:2]};
        }
        if ((source_id.x == 1) && (source_id.y == 1)) {
          destination_id.x inside {[0:3]};
          destination_id.y inside {[0:3]};
        }
      })
    end
  endtask

  `tue_object_default_constructor(tnoc_router_random_test_sequence)
  `uvm_object_utils(tnoc_router_random_test_sequence)
endclass

class tnoc_router_random_test extends tnoc_router_test_base;
  function void start_of_simulation_phase(uvm_phase phase);
    set_default_sequence(sequencer, "main_phase", tnoc_router_random_test_sequence::type_id::get());
  endfunction

  `tue_component_default_constructor(tnoc_router_random_test)
  `uvm_component_utils(tnoc_router_random_test)
endclass
`endif
