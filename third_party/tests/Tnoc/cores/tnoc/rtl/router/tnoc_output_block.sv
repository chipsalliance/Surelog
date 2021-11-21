module tnoc_output_block
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT
)(
  tnoc_types                      types,
  input var logic                 i_clk,
  input var logic                 i_rst_n,
  tnoc_flit_if.receiver           receiver_if[5],
  tnoc_flit_if.sender             sender_if,
  tnoc_port_control_if.controller port_control_if[5]
);
  localparam  int CHANNELS      = PACKET_CONFIG.virtual_channels;
  localparam  int PORT_CHANNELS = (is_local_port(PORT_TYPE)) ? 1 : CHANNELS;
  localparam  int SWITCHES      = (is_local_port(PORT_TYPE)) ? CHANNELS : 1;

//--------------------------------------------------------------
//  Re-order
//--------------------------------------------------------------
  tnoc_flit_if #(
    PACKET_CONFIG, PORT_CHANNELS, PORT_TYPE
  ) port_if[5*SWITCHES](types);

  if (is_local_port(PORT_TYPE)) begin : g_local_port
    for (genvar i = 0;i < CHANNELS;++i) begin : g
      for (genvar j = 0;j < 5;++j) begin : g
        always_comb begin
          port_if[5*i+j].valid        = receiver_if[j].valid[i];
          receiver_if[j].ready[i]     = port_if[5*i+j].ready;
          port_if[5*i+j].flit         = receiver_if[j].flit;
          receiver_if[j].vc_ready[i]  = port_if[5*i+j].vc_ready;
        end
      end
    end
  end
  else begin : g_internal_port
    for (genvar i = 0;i < 5;++i) begin : g
      tnoc_flit_if_connector u_connector (receiver_if[i], port_if[i]);
    end
  end

//--------------------------------------------------------------
//  Port controller
//--------------------------------------------------------------
  logic [SWITCHES-1:0][4:0] output_grant;
  logic [SWITCHES-1:0]      output_free;

  if (is_local_port(PORT_TYPE)) begin : g_local_port_contoller
    tnoc_port_controller_local #(CHANNELS) u_port_controller (
      .i_clk            (i_clk              ),
      .i_rst_n          (i_rst_n            ),
      .i_vc_ready       (sender_if.vc_ready ),
      .port_control_if  (port_control_if    ),
      .o_output_grant   (output_grant       ),
      .i_output_free    (output_free        )
    );
  end
  else begin : g_internal_port_controller
    tnoc_port_contller_internal #(CHANNELS) u_port_controller (
      .i_clk            (i_clk              ),
      .i_rst_n          (i_rst_n            ),
      .i_vc_ready       (sender_if.vc_ready ),
      .port_control_if  (port_control_if    ),
      .o_output_grant   (output_grant       ),
      .i_output_free    (output_free        )
    );
  end

//--------------------------------------------------------------
//  Switch
//--------------------------------------------------------------
  tnoc_types #(PACKET_CONFIG) types_temp(); //  Workaround for VCS's bug
  tnoc_flit_if #(
    PACKET_CONFIG, PORT_CHANNELS, PORT_TYPE
  ) switch_if[SWITCHES](types_temp);

  for (genvar i = 0;i < SWITCHES;++i) begin : g_switch
    tnoc_output_switch #(
      .PACKET_CONFIG  (PACKET_CONFIG  ),
      .PORT_TYPE      (PORT_TYPE      ),
      .CHANNELS       (PORT_CHANNELS  )
    ) u_switch (
      .types          (types                  ),
      .i_clk          (i_clk                  ),
      .i_rst_n        (i_rst_n                ),
      .receiver_if    (port_if[5*i:5*(i+1)-1] ),
      .sender_if      (switch_if[i]           ),
      .i_output_grant (output_grant[i]        ),
      .o_output_free  (output_free[i]         )
    );
  end

  if (is_local_port(PORT_TYPE)) begin : g_vc_mux
    tnoc_vc_mux #(
      .PACKET_CONFIG  (PACKET_CONFIG    ),
      .PORT_TYPE      (TNOC_LOCAL_PORT  )
    ) u_vc_mux (
      .types        (types      ),
      .i_vc_grant   ('0         ),
      .receiver_if  (switch_if  ),
      .sender_if    (sender_if  )
    );
  end
  else begin : g_rename
    tnoc_flit_if_connector u_connector (switch_if[0], sender_if);
  end
endmodule
