module tnoc_vc_arbiter
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT,
  parameter int                 FIFO_DEPTH    = 4
)(
  tnoc_types            types,
  input var logic       i_clk,
  input var logic       i_rst_n,
  tnoc_flit_if.receiver receiver_if,
  tnoc_flit_if.sender   sender_if
);
  localparam  int CHANNELS  = PACKET_CONFIG.virtual_channels;

//--------------------------------------------------------------
//  Split into each VC
//--------------------------------------------------------------
  tnoc_flit_if #(PACKET_CONFIG, 1)  flit_fifo_in_if[CHANNELS](types);
  tnoc_flit_if #(PACKET_CONFIG, 1)  flit_vc_if[CHANNELS](types);

  tnoc_vc_splitter #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .PORT_TYPE      (PORT_TYPE      )
  ) u_vc_splitter (
    .types        (types            ),
    .receiver_if  (receiver_if      ),
    .sender_if    (flit_fifo_in_if  )
  );

  for (genvar i = 0;i < CHANNELS;++i) begin : g_fifo
    if (FIFO_DEPTH > 2) begin : g
      tnoc_flit_if_fifo #(
        .PACKET_CONFIG  (PACKET_CONFIG  ),
        .CHANNELS       (1              ),
        .DEPTH          (FIFO_DEPTH     ),
        .THRESHOLD      (FIFO_DEPTH - 2 )
      ) u_fifo (
        .types          (types            ),
        .i_clk          (i_clk            ),
        .i_rst_n        (i_rst_n          ),
        .i_clear        ('0               ),
        .o_empty        (),
        .o_almost_full  (),
        .o_full         (),
        .receiver_if    (flit_fifo_in_if[i] ),
        .sender_if      (flit_vc_if[i]      )
      );
    end
    else begin : g
      tnoc_flit_if_connector u_connector (
        .receiver_if  (flit_fifo_in_if[i] ),
        .sender_if    (flit_vc_if[i]      )
      );
    end
  end

//--------------------------------------------------------------
//  Arbitration
//--------------------------------------------------------------
  logic [CHANNELS-1:0]  vc_request;
  logic [CHANNELS-1:0]  vc_grant;
  logic [CHANNELS-1:0]  vc_free;

  for (genvar i = 0;i < CHANNELS;++i) begin : g_arbitration
    always_comb begin
      vc_request[i] = flit_vc_if[i].get_head_flit_valid(0);
      vc_free[i]    = flit_vc_if[i].get_tail_flit_ack(0);
    end
  end

  tbcm_round_robin_arbiter #(
    .REQUESTS     (CHANNELS ),
    .KEEP_RESULT  (1        )
  ) u_arbiter (
    .clk        (i_clk      ),
    .rst_n      (i_rst_n    ),
    .i_request  (vc_request ),
    .o_grant    (vc_grant   ),
    .i_free     (vc_free    )
  );

  tnoc_flit_if_mux #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (1              ),
    .ENTRIES        (CHANNELS       )
  ) u_vc_mux (
    .types        (types      ),
    .i_select     (vc_grant   ),
    .receiver_if  (flit_vc_if ),
    .sender_if    (sender_if  )
  );
endmodule
