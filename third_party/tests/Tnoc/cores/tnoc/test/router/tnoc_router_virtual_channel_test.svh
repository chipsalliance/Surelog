`ifndef TNOC_ROUTER_VIRTUAL_CHANNEL_TEST_SVH
`define TNOC_ROUTER_VIRTUAL_CHANNEL_TEST_SVH
class tnoc_router_virtual_channel_test_sequence extends tnoc_router_test_sequence_base;
  tnoc_bfm_location_id  sources[2];
  tnoc_bfm_location_id  destinations[2];

  task body();
    setup();
    fork
      do_noc_access(0);
      do_noc_access(1);
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

  task do_noc_access(int index);
    uvm_sequencer_base      sequencer;
    tnoc_bfm_configuration  bfm_cfg;
    int                     vc[2];

    foreach (configuration.bfm_cfg[i]) begin
      if (
        (configuration.bfm_cfg[i].id_x == sources[index].x) &&
        (configuration.bfm_cfg[i].id_y == sources[index].y)
      ) begin
        sequencer = p_sequencer.bfm_sequencer[i];
        bfm_cfg   = configuration.bfm_cfg[i];
        break;
      end
    end

    void'(std::randomize(vc) with {
      vc[0] != vc[1];
      foreach (vc[i]) {
        vc[i] inside {[0:bfm_cfg.virtual_channels-1]};
      }
    });

    for (int i = 0;i < 20;++i) begin
      tnoc_bfm_packet_item  packet_item;
      `uvm_do_on_with(packet_item, sequencer, {
        vc == local::vc[i%2];
        ((i % 2) == index) -> destination_id == destinations[0];
        ((i % 2) != index) -> destination_id == destinations[1];
      })
    end
  endtask

  `tue_object_default_constructor(tnoc_router_virtual_channel_test_sequence)
  `uvm_object_utils(tnoc_router_virtual_channel_test_sequence)
endclass

class tnoc_router_virtual_channel_test extends tnoc_router_test_base;
  function void start_of_simulation_phase(uvm_phase phase);
    set_default_sequence(sequencer, "main_phase", tnoc_router_virtual_channel_test_sequence::type_id::get());
  endfunction

  `tue_component_default_constructor(tnoc_router_virtual_channel_test)
  `uvm_component_utils(tnoc_router_virtual_channel_test)
endclass
`endif
