module tnoc_flit_if_slicer
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter int                 STAGES        = 1,
  parameter int                 CHANNELS      = PACKET_CONFIG.virtual_channels,
  parameter tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT,
  parameter bit                 INTER_ROUTER  = 1
)(
  tnoc_types            types,
  input var logic       i_clk,
  input var logic       i_rst_n,
  tnoc_flit_if.receiver receiver_if,
  tnoc_flit_if.sender   sender_if
);
  tnoc_flit_if #(
    PACKET_CONFIG, CHANNELS, PORT_TYPE
  ) flit_if[STAGES+1](types);

  tnoc_flit_if_connector u_receiver_connector (receiver_if, flit_if[0]);
  tnoc_flit_if_connector u_sender_connector (flit_if[STAGES], sender_if);

  for (genvar i = 0;i < STAGES;++i) begin : g_slicer
    localparam  int DEPTH     = ((i == 0) && INTER_ROUTER) ? 4 : 2;
    localparam  int THRESHOLD = 2;

    tnoc_flit_if_fifo #(
      .PACKET_CONFIG  (PACKET_CONFIG  ),
      .CHANNELS       (CHANNELS       ),
      .DEPTH          (DEPTH          ),
      .THRESHOLD      (THRESHOLD      ),
      .DATA_FF_OUT    (1              ),
      .PORT_TYPE      (PORT_TYPE      )
    ) u_flicer_fifo (
      .types          (types        ),
      .i_clk          (i_clk        ),
      .i_rst_n        (i_rst_n      ),
      .i_clear        ('0           ),
      .o_empty        (),
      .o_almost_full  (),
      .o_full         (),
      .receiver_if    (flit_if[i+0] ),
      .sender_if      (flit_if[i+1] )
    );
  end
endmodule
