`ifndef TNOC_ROUTER_DIFFERENT_ROUTE_TEST_SEQUENCE_SVH
`define TNOC_ROUTER_DIFFERENT_ROUTE_TEST_SEQUENCE_SVH
class tnoc_router_different_route_test_sequence extends tnoc_router_test_sequence_base;
  tnoc_bfm_location_id  sources[2];
  tnoc_bfm_location_id  destinations[2];

  task body();
    setup();
    fork
      do_noc_accesses(sources[0], destinations[0]);
      do_noc_accesses(sources[1], destinations[1]);
    join
  endtask

  function void setup();
    tnoc_bfm_location_id  port_list[5]  = '{
      get_location_id(1, 2), get_location_id(1, 0),
      get_location_id(2, 1), get_location_id(0, 1),
      get_location_id(1, 1)
    };

    port_list.shuffle();
    sources[0]  = port_list[0];
    sources[1]  = port_list[1];

    port_list.shuffle();
    destinations[0] = port_list[0];
    destinations[1] = port_list[1];
  endfunction

  task do_noc_accesses(
    tnoc_bfm_location_id  source,
    tnoc_bfm_location_id  destination
  );
    int index;

    foreach (configuration.bfm_cfg[i]) begin
      if (
        (configuration.bfm_cfg[i].id_x == source.x) &&
        (configuration.bfm_cfg[i].id_y == source.y)
      ) begin
        index = i;
        break;
      end
    end

    repeat (20) begin
      tnoc_bfm_packet_item  packet_item;
      `uvm_do_on_with(packet_item, p_sequencer.bfm_sequencer[index], {
        destination_id == local::destination;
      })
    end
  endtask

  `tue_object_default_constructor(tnoc_router_different_route_test_sequence)
  `uvm_object_utils(tnoc_router_different_route_test_sequence)
endclass

class tnoc_router_different_route_test extends tnoc_router_test_base;
  function void start_of_simulation_phase(uvm_phase phase);
    set_default_sequence(sequencer, "main_phase", tnoc_router_different_route_test_sequence::type_id::get());
  endfunction

  `tue_component_default_constructor(tnoc_router_different_route_test)
  `uvm_component_utils(tnoc_router_different_route_test)
endclass
`endif
