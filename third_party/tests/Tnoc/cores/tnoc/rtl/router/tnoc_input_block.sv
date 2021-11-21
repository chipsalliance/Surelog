module tnoc_input_block
  import  tnoc_pkg::*;
#(
  parameter   tnoc_packet_config                  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter   tnoc_port_type                      PORT_TYPE     = TNOC_LOCAL_PORT,
  parameter   bit [4:0]                           ACTIVE_PORTS  = 5'b11111,
  parameter   int                                 FIFO_DEPTH    = 4,
  parameter   bit                                 ERROR_CHECK   = 1,
  parameter   bit [PACKET_CONFIG.data_width-1:0]  ERROR_DATA    = '1,
  localparam  int                                 ID_X_WIDTH    = get_id_x_width(PACKET_CONFIG),
  localparam  int                                 ID_Y_WIDTH    = get_id_y_width(PACKET_CONFIG)
)(
  tnoc_types  types,
  input var logic                   i_clk,
  input var logic                   i_rst_n,
  input var logic [ID_X_WIDTH-1:0]  i_id_x,
  input var logic [ID_Y_WIDTH-1:0]  i_id_y,
  tnoc_flit_if.receiver             receiver_if,
  tnoc_flit_if.sender               sender_if[5],
  tnoc_port_control_if.requester    port_control_if[5]
);
  localparam  int CHANNELS  = PACKET_CONFIG.virtual_channels;

  tnoc_flit_if #(PACKET_CONFIG, 1)  flit_if[2*CHANNELS](types);

//--------------------------------------------------------------
//  Input FIFO
//--------------------------------------------------------------
  tnoc_input_fifo #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .PORT_TYPE      (PORT_TYPE      ),
    .DEPTH          (FIFO_DEPTH     )
  ) u_finput_fifo (
    .types        (types                              ),
    .i_clk        (i_clk                              ),
    .i_rst_n      (i_rst_n                            ),
    .receiver_if  (receiver_if                        ),
    .sender_if    (flit_if[CHANNELS*0:CHANNELS*1-1  ] )
  );

//--------------------------------------------------------------
//  Error Check
//--------------------------------------------------------------
  if (is_local_port(PORT_TYPE) && ERROR_CHECK) begin : g_error_checker
    for (genvar i = 0;i < CHANNELS;++i) begin : g
      tnoc_error_checker #(
        .PACKET_CONFIG  (PACKET_CONFIG  ),
        .ERROR_DATA     (ERROR_DATA     )
      ) u_error_checker (
        .types        (types                ),
        .i_clk        (i_clk                ),
        .i_rst_n      (i_rst_n              ),
        .receiver_if  (flit_if[i]           ),
        .sender_if    (flit_if[CHANNELS+i]  )
      );
    end
  end
  else begin : g_no_error_checker
    for (genvar i = 0;i < CHANNELS;++i) begin : g
      tnoc_flit_if_connector u_connector (flit_if[i], flit_if[CHANNELS+i]);
    end
  end

//--------------------------------------------------------------
//  Route selector
//--------------------------------------------------------------
  tnoc_route_selector #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .ACTIVE_PORTS   (ACTIVE_PORTS   )
  ) u_route_selector (
    .types            (types                            ),
    .i_clk            (i_clk                            ),
    .i_rst_n          (i_rst_n                          ),
    .i_id_x           (i_id_x                           ),
    .i_id_y           (i_id_y                           ),
    .port_control_if  (port_control_if                  ),
    .receiver_if      (flit_if[1*CHANNELS:2*CHANNELS-1] ),
    .sender_if        (sender_if                        )
  );
endmodule
