module tnoc_axi_slave_adapter
  import  tnoc_pkg::*,
          tnoc_axi_pkg::*;
#(
  parameter   tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter   tnoc_axi_config     AXI_CONFIG    = TNOC_DEFAULT_AXI_CONFIG,
  parameter   int                 FIFO_DEPTH    = 4,
  localparam  int                 ID_X_WIDTH    = get_id_x_width(PACKET_CONFIG),
  localparam  int                 ID_Y_WIDTH    = get_id_y_width(PACKET_CONFIG),
  localparam  int                 VC_WIDTH      = get_vc_width(PACKET_CONFIG)
)(
  tnoc_types                        packet_types,
  tnoc_axi_types                    axi_types,
  input var logic                   i_clk,
  input var logic                   i_rst_n,
  input var logic [ID_X_WIDTH-1:0]  i_id_x,
  input var logic [ID_Y_WIDTH-1:0]  i_id_y,
  input var logic [VC_WIDTH-1:0]    i_request_base_vc,
  tnoc_address_decoder_if.requester write_decoder_if,
  tnoc_address_decoder_if.requester read_decoder_if,
  tnoc_axi_if.slave                 axi_if,
  tnoc_flit_if.receiver             receiver_if,
  tnoc_flit_if.sender               sender_if
);
  tnoc_flit_if #(
    PACKET_CONFIG, 1, TNOC_LOCAL_PORT
  ) flit_if[4](packet_types);

//--------------------------------------------------------------
//  AXI Write/Read Channels
//--------------------------------------------------------------
  tnoc_axi_if #(AXI_CONFIG) axi_write_read_if(axi_types);
  tnoc_axi_if_connector u_axi_if_connector (
    axi_if, axi_write_read_if
  );

  tnoc_axi_slave_write_adapter #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .AXI_CONFIG     (AXI_CONFIG     ),
    .ID_X_WIDTH     (ID_X_WIDTH     ),
    .ID_Y_WIDTH     (ID_Y_WIDTH     ),
    .VC_WIDTH       (VC_WIDTH       )
  ) u_write_adapter (
    .packet_types (packet_types       ),
    .axi_types    (axi_types          ),
    .i_clk        (i_clk              ),
    .i_rst_n      (i_rst_n            ),
    .i_id_x       (i_id_x             ),
    .i_id_y       (i_id_y             ),
    .i_base_vc    (i_request_base_vc  ),
    .decoder_if   (write_decoder_if   ),
    .axi_if       (axi_write_read_if  ),
    .receiver_if  (flit_if[0]         ),
    .sender_if    (flit_if[1]         )
  );

  tnoc_axi_slave_read_adapter #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .AXI_CONFIG     (AXI_CONFIG     ),
    .ID_X_WIDTH     (ID_X_WIDTH     ),
    .ID_Y_WIDTH     (ID_Y_WIDTH     ),
    .VC_WIDTH       (VC_WIDTH       )
  ) u_read_adapter (
    .packet_types (packet_types       ),
    .axi_types    (axi_types          ),
    .i_clk        (i_clk              ),
    .i_rst_n      (i_rst_n            ),
    .i_id_x       (i_id_x             ),
    .i_id_y       (i_id_y             ),
    .i_base_vc    (i_request_base_vc  ),
    .decoder_if   (read_decoder_if    ),
    .axi_if       (axi_write_read_if  ),
    .receiver_if  (flit_if[2]         ),
    .sender_if    (flit_if[3]         )
  );

//--------------------------------------------------------------
//  MUX/DEMUX
//--------------------------------------------------------------
  tnoc_axi_write_read_demux #(
    .PACKET_CONFIG  (PACKET_CONFIG            ),
    .WRITE_TYPE     (TNOC_RESPONSE            ),
    .READ_TYPE      (TNOC_RESPONSE_WITH_DATA  ),
    .FIFO_DEPTH     (FIFO_DEPTH               )
  ) u_write_read_demux (
    .types        (packet_types ),
    .i_clk        (i_clk        ),
    .i_rst_n      (i_rst_n      ),
    .receiver_if  (receiver_if  ),
    .write_if     (flit_if[0]   ),
    .read_if      (flit_if[2]   )
  );

  tnoc_axi_write_read_mux #(
    .PACKET_CONFIG  (PACKET_CONFIG  )
  ) u_write_read_mux (
    .types      (packet_types ),
    .i_clk      (i_clk        ),
    .i_rst_n    (i_rst_n      ),
    .write_if   (flit_if[1]   ),
    .read_if    (flit_if[3]   ),
    .sender_if  (sender_if    )
  );
endmodule
