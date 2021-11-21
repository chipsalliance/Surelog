module tnoc_router
  import  tnoc_pkg::*;
#(
  parameter   tnoc_packet_config                  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter   bit [4:0]                           ACTIVE_PORTS  = 5'b11111,
  parameter   int                                 FIFO_DEPTH    = 4,
  parameter   bit                                 ERROR_CHECK   = 1,
  parameter   bit [PACKET_CONFIG.data_width-1:0]  ERROR_DATA    = '1,
  localparam  int                                 ID_X_WIDTH    = get_id_x_width(PACKET_CONFIG),
  localparam  int                                 ID_Y_WIDTH    = get_id_y_width(PACKET_CONFIG)
)(
  tnoc_types                        types,
  input var logic                   i_clk,
  input var logic                   i_rst_n,
  input var logic [ID_X_WIDTH-1:0]  i_id_x,
  input var logic [ID_Y_WIDTH-1:0]  i_id_y,
  tnoc_flit_if.receiver             receiver_if_xp,
  tnoc_flit_if.sender               sender_if_xp,
  tnoc_flit_if.receiver             receiver_if_xm,
  tnoc_flit_if.sender               sender_if_xm,
  tnoc_flit_if.receiver             receiver_if_yp,
  tnoc_flit_if.sender               sender_if_yp,
  tnoc_flit_if.receiver             receiver_if_ym,
  tnoc_flit_if.sender               sender_if_ym,
  tnoc_flit_if.receiver             receiver_if_local,
  tnoc_flit_if.sender               sender_if_local
);
  function automatic tnoc_port_type get_port_type(int port_index);
    if (port_index == 4) begin
      return TNOC_LOCAL_PORT;
    end
    else begin
      return TNOC_INTERNAL_PORT;
    end
  endfunction

  tnoc_flit_if #(
    .PACKET_CONFIG  (PACKET_CONFIG      ),
    .PORT_TYPE      (TNOC_INTERNAL_PORT )
  ) input_block_flit_if[25](types);
  tnoc_flit_if #(
    .PACKET_CONFIG  (PACKET_CONFIG      ),
    .PORT_TYPE      (TNOC_INTERNAL_PORT )
  ) output_block_flit_if[25](types);

  tnoc_port_control_if #(
    .PACKET_CONFIG  (PACKET_CONFIG  )
  ) input_block_port_control_if[25]();
  tnoc_port_control_if #(
    .PACKET_CONFIG  (PACKET_CONFIG  )
  ) output_block_port_control_if[25]();

  for (genvar i = 0;i < 5;++i) begin : g_input_block
    localparam  tnoc_port_type  PORT_TYPE = get_port_type(i);

    tnoc_flit_if #(
      .PACKET_CONFIG  (PACKET_CONFIG  ),
      .PORT_TYPE      (PORT_TYPE      )
    ) receiver_if(types);

    if (i == 0) begin : g_xp
      tnoc_flit_if_connector u_connector (receiver_if_xp, receiver_if);
    end
    else if (i == 1) begin : g_xm
      tnoc_flit_if_connector u_connector (receiver_if_xm, receiver_if);
    end
    else if (i == 2) begin : g_yp
      tnoc_flit_if_connector u_connector (receiver_if_yp, receiver_if);
    end
    else if (i == 3) begin : g_ym
      tnoc_flit_if_connector u_connector (receiver_if_ym, receiver_if);
    end
    else begin : g_local
      tnoc_flit_if_connector u_connector (receiver_if_local, receiver_if);
    end

    if (ACTIVE_PORTS[i]) begin : g
      tnoc_input_block #(
        .PACKET_CONFIG  (PACKET_CONFIG  ),
        .PORT_TYPE      (PORT_TYPE      ),
        .ACTIVE_PORTS   (ACTIVE_PORTS   ),
        .FIFO_DEPTH     (FIFO_DEPTH     ),
        .ERROR_CHECK    (ERROR_CHECK    ),
        .ERROR_DATA     (ERROR_DATA     )
      ) u_input_block (
        .types            (types                                      ),
        .i_clk            (i_clk                                      ),
        .i_rst_n          (i_rst_n                                    ),
        .i_id_x           (i_id_x                                     ),
        .i_id_y           (i_id_y                                     ),
        .receiver_if      (receiver_if                                ),
        .sender_if        (input_block_flit_if[5*i:5*(i+1)-1]         ),
        .port_control_if  (input_block_port_control_if[5*i:5*(i+1)-1] )
      );
    end
    else begin : g_dummy
      tnoc_input_block_dummy #(
        .PACKET_CONFIG  (PACKET_CONFIG  )
      ) u_dummy (
        .receiver_if      (receiver_if                                ),
        .sender_if        (input_block_flit_if[5*i:5*(i+1)-1]         ),
        .port_control_if  (input_block_port_control_if[5*i:5*(i+1)-1] )
      );
    end
  end

  tnoc_if_transposer u_if_transposer (
    .receiver_if    (input_block_flit_if          ),
    .controller_if  (input_block_port_control_if  ),
    .sender_if      (output_block_flit_if         ),
    .requester_if   (output_block_port_control_if )
  );

  for (genvar i = 0;i < 5;++i) begin : g_output_block
    localparam  tnoc_port_type  PORT_TYPE = get_port_type(i);

    tnoc_flit_if #(
      .PACKET_CONFIG  (PACKET_CONFIG  ),
      .PORT_TYPE      (PORT_TYPE      )
    ) sender_if(types);

    if (i == 0) begin : g_xp
      tnoc_flit_if_connector u_connector (sender_if, sender_if_xp);
    end
    else if (i == 1) begin : g_xm
      tnoc_flit_if_connector u_connector (sender_if, sender_if_xm);
    end
    else if (i == 2) begin : g_yp
      tnoc_flit_if_connector u_connector (sender_if, sender_if_yp);
    end
    else if (i == 3) begin : g_ym
      tnoc_flit_if_connector u_connector (sender_if, sender_if_ym);
    end
    else begin : g_local
      tnoc_flit_if_connector u_connector (sender_if, sender_if_local);
    end

    if (ACTIVE_PORTS[i]) begin : g
      tnoc_output_block #(
        .PACKET_CONFIG  (PACKET_CONFIG  ),
        .PORT_TYPE      (PORT_TYPE      )
      ) u_output_block (
        .types            (types                                        ),
        .i_clk            (i_clk                                        ),
        .i_rst_n          (i_rst_n                                      ),
        .receiver_if      (output_block_flit_if[5*i:5*(i+1)-1]          ),
        .sender_if        (sender_if                                    ),
        .port_control_if  (output_block_port_control_if[5*i:5*(i+1)-1]  )
      );
    end
    else begin : g_dummy
      tnoc_output_block_dummy #(
        .PACKET_CONFIG  (PACKET_CONFIG  )
      ) u_dummy (
        .receiver_if      (output_block_flit_if[5*i:5*(i+1)-1]          ),
        .sender_if        (sender_if                                    ),
        .port_control_if  (output_block_port_control_if[5*i:5*(i+1)-1]  )
      );
    end
  end
endmodule
