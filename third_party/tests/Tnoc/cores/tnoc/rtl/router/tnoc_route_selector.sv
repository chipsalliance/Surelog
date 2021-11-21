module tnoc_route_selector
  import  tnoc_pkg::*;
#(
  parameter   tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter   bit [4:0]           ACTIVE_PORTS  = 5'b11111,
  localparam  int                 CHANNELS      = PACKET_CONFIG.virtual_channels,
  localparam  int                 ID_X_WIDTH    = get_id_x_width(PACKET_CONFIG),
  localparam  int                 ID_Y_WIDTH    = get_id_y_width(PACKET_CONFIG)
)(
  tnoc_types                        types,
  input var logic                   i_clk,
  input var logic                   i_rst_n,
  input var logic [ID_X_WIDTH-1:0]  i_id_x,
  input var logic [ID_Y_WIDTH-1:0]  i_id_y,
  tnoc_port_control_if.requester    port_control_if[5],
  tnoc_flit_if.receiver             receiver_if[CHANNELS],
  tnoc_flit_if.sender               sender_if[5]
);
  typedef enum logic [4:0] {
    ROUTE_X_PLUS  = 5'b00001,
    ROUTE_X_MINUS = 5'b00010,
    ROUTE_Y_PLUS  = 5'b00100,
    ROUTE_Y_MINUS = 5'b01000,
    ROUTE_LOCAL   = 5'b10000,
    ROUTE_NA      = 5'b00000
  } e_route;

  typedef types.tnoc_flit           tnoc_flit;
  typedef types.tnoc_location_id    tnoc_location_id;
  typedef types.tnoc_common_header  tnoc_common_header;

//--------------------------------------------------------------
//  Routing
//--------------------------------------------------------------
  tnoc_flit_if #(PACKET_CONFIG, 1)  routed_if[5*CHANNELS](types);

  for (genvar i = 0;i < CHANNELS;++i) begin : g_routing
    e_route route;
    e_route route_latched;

    always_comb begin
      route = (
        receiver_if[i].flit[0].head
      ) ? select_route(receiver_if[i].flit[0]) : route_latched;
    end

    always_ff @(posedge i_clk) begin
      if (receiver_if[i].get_head_flit_valid(0)) begin
        route_latched <= route;
      end
    end

    for (genvar j = 0;j < 5;++j) begin : g
      always_comb begin
        if (route[j] && ACTIVE_PORTS[j]) begin
          port_control_if[j].request[i]         = receiver_if[i].valid;
          port_control_if[j].free[i]            = receiver_if[i].ready;
          port_control_if[j].start_of_packet[i] = receiver_if[i].get_head_flit_valid(0);
          port_control_if[j].end_of_packet[i]   = receiver_if[i].get_tail_flit_ack(0);
        end
        else begin
          port_control_if[j].request[i]         = '0;
          port_control_if[j].free[i]            = '0;
          port_control_if[j].start_of_packet[i] = '0;
          port_control_if[j].end_of_packet[i]   = '0;
        end
      end
    end

    tnoc_flit_if_demux #(
      .PACKET_CONFIG  (PACKET_CONFIG  ),
      .CHANNELS       (1              ),
      .ENTRIES        (5              )
    ) u_demux (
      .types        (types                    ),
      .i_select     (route                    ),
      .receiver_if  (receiver_if[i]           ),
      .sender_if    (routed_if[5*i:5*(i+1)-1] )
    );
  end

  function automatic e_route select_route(tnoc_flit flit);
    tnoc_common_header  header;
    tnoc_location_id    destination_id;
    logic [3:0]         result;

    header          = tnoc_common_header'(flit.data);
    destination_id  = header.destination_id;

    result[0] = (destination_id.x > i_id_x) ? ACTIVE_PORTS[0] : '0;
    result[1] = (destination_id.x < i_id_x) ? ACTIVE_PORTS[1] : '0;
    result[2] = (destination_id.y > i_id_y) ? ACTIVE_PORTS[2] : '0;
    result[3] = (destination_id.y < i_id_y) ? ACTIVE_PORTS[3] : '0;

    case (1'b1)
      result[0]:  return ROUTE_X_PLUS;
      result[1]:  return ROUTE_X_MINUS;
      result[2]:  return ROUTE_Y_PLUS;
      result[3]:  return ROUTE_Y_MINUS;
      default:    return ROUTE_LOCAL;
    endcase
  endfunction

//--------------------------------------------------------------
//  VC Merging
//--------------------------------------------------------------
  tnoc_flit_if #(PACKET_CONFIG, 1)  vc_if[5*CHANNELS](types);

  for (genvar i = 0;i < 5;++i) begin : g_vc_merging
    for (genvar j = 0;j < CHANNELS;++j) begin : g_connector
      tnoc_flit_if_connector u_connector (routed_if[5*j+i], vc_if[CHANNELS*i+j]);
    end

    if (ACTIVE_PORTS[i]) begin : g
      tnoc_vc_merger #(
        .PACKET_CONFIG  (PACKET_CONFIG  )
      ) u_merger (
        .types        (types                              ),
        .i_clk        (i_clk                              ),
        .i_rst_n      (i_rst_n                            ),
        .i_vc_grant   (port_control_if[i].grant           ),
        .receiver_if  (vc_if[CHANNELS*i:CHANNELS*(i+1)-1] ),
        .sender_if    (sender_if[i]                       )
      );
    end
    else begin : g_dummy
      tnoc_flit_if_dummy_sender u_dummy_sender (sender_if[i]);

      tnoc_flit_if_dummy_receiver_array #(
        .PACKET_CONFIG  (PACKET_CONFIG  ),
        .CHANNELS       (1              ),
        .ENTRIES        (CHANNELS       )
      ) u_dummy_receiver (
        vc_if[CHANNELS*i:CHANNELS*(i+1)-1]
      );
    end
  end
endmodule
