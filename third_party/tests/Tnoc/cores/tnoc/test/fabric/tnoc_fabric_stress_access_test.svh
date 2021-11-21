`ifndef TNOC_FABRIC_STRESS_ACCESS_TEST_SVH
`define TNOC_FABRIC_STRESS_ACCESS_TEST_SVH
class tnoc_fabric_stress_access_test_sequence extends tnoc_fabric_test_sequence_base;
  task body();
    stress_access_test(0);
    stress_access_test(1);
    stress_access_test(2);
    stress_access_test(3);
  endtask

  task stress_access_test(int test_mode);
    tnoc_bfm_location_id  destination;

    void'(std::randomize(destination) with {
      destination.x inside {[0:configuration.size_x-1]};
      destination.y inside {[0:configuration.size_y-1]};
    });

    foreach (p_sequencer.bfm_sequencer[y, x]) begin
      fork
        automatic uvm_sequencer_base  sequencer = p_sequencer.bfm_sequencer[y][x];
        do_noc_access(sequencer, destination, test_mode);
      join_none
    end

    wait fork;
  endtask

  task do_noc_access(uvm_sequencer_base sequencer, tnoc_bfm_location_id destination, int test_mode);
    for (int i = 0;i < 20;++i) begin
      tnoc_bfm_packet_item  packet_item;
      `uvm_do_on_with(packet_item, sequencer, {
        destination_id == destination;
        burst_length   >= 8;
        if (test_mode inside {[0:2]}) {
           packet_type inside {TNOC_BFM_RESPONSE, TNOC_BFM_RESPONSE_WITH_DATA};
        }
        else if (test_mode inside {[3:5]}) {
          packet_type inside {TNOC_BFM_READ, TNOC_BFM_POSTED_WRITE, TNOC_BFM_NON_POSTED_WRITE};
        }
        else if (test_mode inside {[6:8]}) {
          ((i % 2) == 0) -> packet_type inside {TNOC_BFM_RESPONSE, TNOC_BFM_RESPONSE_WITH_DATA};
          ((i % 2) == 1) -> packet_type inside {TNOC_BFM_READ, TNOC_BFM_POSTED_WRITE, TNOC_BFM_NON_POSTED_WRITE};
        }
      })
    end
  endtask

  `tue_object_default_constructor(tnoc_fabric_stress_access_test_sequence)
  `uvm_object_utils(tnoc_fabric_stress_access_test_sequence)
endclass

class tnoc_fabric_stress_access_test extends tnoc_fabric_test_base;
  function void start_of_simulation_phase(uvm_phase phase);
    set_default_sequence(sequencer, "main_phase", tnoc_fabric_stress_access_test_sequence::type_id::get());
  endfunction

  `tue_component_default_constructor(tnoc_fabric_stress_access_test)
  `uvm_component_utils(tnoc_fabric_stress_access_test)
endclass
`endif
