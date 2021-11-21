/*
:name: TNoC
:description: Full TNoC core test
:files: /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/bcm/tbcm_counter.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/bcm/tbcm_fifo.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/bcm/tbcm_mux.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/bcm/tbcm_demux.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/bcm/tbcm_selector.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/bcm/tbcm_onehot.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/bcm/tbcm_round_robin_arbiter.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/bcm/tbcm_crc_pkg.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/bcm/tbcm_crc.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_pkg.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_types.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_utils.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_flit_if.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_flit_if_connector.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_flit_if_dummy_receiver.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_flit_if_dummy_receiver_array.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_flit_if_dummy_sender.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_flit_if_dummy_sender_array.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_flit_if_mux.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_flit_if_demux.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_flit_if_fifo.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_flit_if_slicer.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_vc_arbiter.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_vc_splitter.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_vc_mux.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_packet_if.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_packet_serializer.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_packet_deserializer.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/common/tnoc_address_decoder_if.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_port_control_if.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_port_controller_local.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_port_controller_internal.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_input_fifo.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_error_checker.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_vc_merger.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_route_selector.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_input_block.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_input_block_dummy.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_output_switch.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_output_block.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_output_block_dummy.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_if_transposer.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/router/tnoc_router.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/fabric/tnoc_dummy_node.sv /home/alain/alain-marcel/sv-tests/third_party/cores/tnoc/rtl/fabric/tnoc_fabric.sv /home/alain/alain-marcel/sv-tests/tests/generated/tnoc/tnoc.sv
:tags: TNoC
:top_module: tnoc
:timeout: 100
*/

module tnoc (
  input var i_clk,
  input var i_rst_n
);
  import  tnoc_pkg::*;

  localparam  tnoc_packet_config  PACKET_CONFIG = '{
    size_x:           3,
    size_y:           3,
    virtual_channels: 2,
    tags:             32,
    address_width:    64,
    data_width:       64,
    max_data_width:   64,
    max_byte_length:  32 * (64 / 8)
  };

  tnoc_types #(PACKET_CONFIG)   types();
  tnoc_flit_if #(PACKET_CONFIG) receiver_if[9](types);
  tnoc_flit_if #(PACKET_CONFIG) sender_if[9](types);

  tnoc_fabric #(PACKET_CONFIG) u_fabric (.*);
endmodule
