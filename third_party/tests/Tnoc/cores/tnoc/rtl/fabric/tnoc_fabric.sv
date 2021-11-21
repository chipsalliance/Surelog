module tnoc_fabric
  import  tnoc_pkg::*;
#(
  parameter   tnoc_packet_config                  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter   int                                 FIFO_DEPTH    = 4,
  parameter   bit                                 ERROR_CHECK   = 1,
  parameter   bit [PACKET_CONFIG.data_width-1:0]  ERROR_DATA    = '1,
  localparam  int                                 SIZE_X        = PACKET_CONFIG.size_x,
  localparam  int                                 SIZE_Y        = PACKET_CONFIG.size_y,
  localparam  int                                 TOTAL_ROUTERS = SIZE_X * SIZE_Y
)(
  tnoc_types            types,
  input var logic       i_clk,
  input var logic       i_rst_n,
  tnoc_flit_if.receiver receiver_if[TOTAL_ROUTERS],
  tnoc_flit_if.sender   sender_if[TOTAL_ROUTERS]
);
  typedef logic [get_id_x_width(PACKET_CONFIG)-1:0] tnoc_id_x;
  typedef logic [get_id_y_width(PACKET_CONFIG)-1:0] tnoc_id_y;

  localparam  int FLIT_IF_SIZE_X  = (SIZE_X + 1) * SIZE_Y;
  localparam  int FLIT_IF_SIZE_Y  = (SIZE_Y + 1) * SIZE_X;

  tnoc_flit_if #(PACKET_CONFIG) flit_if_x_p2m[FLIT_IF_SIZE_X](types);
  tnoc_flit_if #(PACKET_CONFIG) flit_if_x_m2p[FLIT_IF_SIZE_X](types);
  tnoc_flit_if #(PACKET_CONFIG) flit_if_y_p2m[FLIT_IF_SIZE_Y](types);
  tnoc_flit_if #(PACKET_CONFIG) flit_if_y_m2p[FLIT_IF_SIZE_Y](types);

  for (genvar y = 0;y < SIZE_Y;++y) begin : g_y
    for (genvar x = 0;x < SIZE_X;++x) begin : g_x
      localparam  int       INDEX_X       = (SIZE_X + 1) * y + x;
      localparam  int       INDEX_Y       = (SIZE_Y + 1) * x + y;
      localparam  int       INDEX_L       = (SIZE_X + 0) * y + x;
      localparam  tnoc_id_x ID_X          = x;
      localparam  tnoc_id_y ID_Y          = y;
      localparam  bit [4:0] ACTIVE_PORTS  = get_active_ports(y, x);

      tnoc_router #(
        .PACKET_CONFIG  (PACKET_CONFIG  ),
        .ACTIVE_PORTS   (ACTIVE_PORTS   ),
        .FIFO_DEPTH     (FIFO_DEPTH     ),
        .ERROR_CHECK    (ERROR_CHECK    ),
        .ERROR_DATA     (ERROR_DATA     )
      ) u_router (
        .types              (types                    ),
        .i_clk              (i_clk                    ),
        .i_rst_n            (i_rst_n                  ),
        .i_id_x             (ID_X                     ),
        .i_id_y             (ID_Y                     ),
        .receiver_if_xp     (flit_if_x_m2p[INDEX_X+1] ),
        .sender_if_xp       (flit_if_x_p2m[INDEX_X+1] ),
        .receiver_if_xm     (flit_if_x_p2m[INDEX_X+0] ),
        .sender_if_xm       (flit_if_x_m2p[INDEX_X+0] ),
        .receiver_if_yp     (flit_if_y_m2p[INDEX_Y+1] ),
        .sender_if_yp       (flit_if_y_p2m[INDEX_Y+1] ),
        .receiver_if_ym     (flit_if_y_p2m[INDEX_Y+0] ),
        .sender_if_ym       (flit_if_y_m2p[INDEX_Y+0] ),
        .receiver_if_local  (receiver_if[INDEX_L]     ),
        .sender_if_local    (sender_if[INDEX_L]       )
      );

      if (!ACTIVE_PORTS[0]) begin : g_dummy_xp
        tnoc_dummy_node u_dummy (
          .receiver_if  (flit_if_x_p2m[INDEX_X+1] ),
          .sender_if    (flit_if_x_m2p[INDEX_X+1] )
        );
      end

      if (!ACTIVE_PORTS[1]) begin : g_dummy_xm
        tnoc_dummy_node u_dummy (
          .receiver_if  (flit_if_x_m2p[INDEX_X+0] ),
          .sender_if    (flit_if_x_p2m[INDEX_X+0] )
        );
      end

      if (!ACTIVE_PORTS[2]) begin : g_dummy_yp
        tnoc_dummy_node u_dummy (
          .receiver_if  (flit_if_y_p2m[INDEX_Y+1] ),
          .sender_if    (flit_if_y_m2p[INDEX_Y+1] )
        );
      end

      if (!ACTIVE_PORTS[3]) begin : g_dummy_ym
        tnoc_dummy_node u_dummy (
          .receiver_if  (flit_if_y_m2p[INDEX_Y+0] ),
          .sender_if    (flit_if_y_p2m[INDEX_Y+0] )
        );
      end
    end
  end

  function automatic bit [4:0] get_active_ports(int y, int x);
    bit [4:0] active_ports;
    active_ports[0] = (x < (SIZE_X - 1)) ? 1 : 0;
    active_ports[1] = (x > 0           ) ? 1 : 0;
    active_ports[2] = (y < (SIZE_Y - 1)) ? 1 : 0;
    active_ports[3] = (y > 0           ) ? 1 : 0;
    active_ports[4] = 1;
    return active_ports;
  endfunction
endmodule
