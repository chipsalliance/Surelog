module tnoc_vc_merger
  import  tnoc_pkg::*;
#(
  parameter   tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  localparam  int                 CHANNELS      = PACKET_CONFIG.virtual_channels
)(
  tnoc_types                      types,
  input var logic                 i_clk,
  input var logic                 i_rst_n,
  input var logic [CHANNELS-1:0]  i_vc_grant,
  tnoc_flit_if.receiver           receiver_if[CHANNELS],
  tnoc_flit_if.sender             sender_if
);
  tnoc_flit_if #(
    .PACKET_CONFIG  (PACKET_CONFIG      ),
    .PORT_TYPE      (TNOC_INTERNAL_PORT )
  ) flit_if(types);

  tnoc_vc_mux #(
    .PACKET_CONFIG  (PACKET_CONFIG      ),
    .PORT_TYPE      (TNOC_INTERNAL_PORT )
  ) u_vc_mux (
    .types        (types        ),
    .i_vc_grant   (i_vc_grant   ),
    .receiver_if  (receiver_if  ),
    .sender_if    (flit_if      )
  );

  tnoc_flit_if_slicer #(
    .PACKET_CONFIG  (PACKET_CONFIG      ),
    .PORT_TYPE      (TNOC_INTERNAL_PORT ),
    .INTER_ROUTER   (0                  )
  ) u_slicer (
    .types        (types      ),
    .i_clk        (i_clk      ),
    .i_rst_n      (i_rst_n    ),
    .receiver_if  (flit_if    ),
    .sender_if    (sender_if  )
  );
endmodule
