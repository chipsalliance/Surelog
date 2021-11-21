module tnoc_port_controller_local
  import  tnoc_pkg::*;
#(
  parameter int CHANNELS  = TNOC_DEFAULT_PACKET_CONFIG.virtual_channels
)(
  input   var logic                     i_clk,
  input   var logic                     i_rst_n,
  input   var logic [CHANNELS-1:0]      i_vc_ready,
  tnoc_port_control_if.controller       port_control_if[5],
  output  var logic [CHANNELS-1:0][4:0] o_output_grant,
  input   var logic [CHANNELS-1:0]      i_output_free
);
//--------------------------------------------------------------
//  Port Arbitration
//--------------------------------------------------------------
  logic [CHANNELS-1:0][4:0] port_grant;

  for (genvar i = 0;i < CHANNELS;++i) begin : g_port_arbitration
    logic [4:0] port_request;
    logic [4:0] port_free;

    for (genvar j = 0;j < 5;++j) begin : g
      always_comb begin
        port_request[j] = port_control_if[j].start_of_packet[i];
        port_free[j]    = port_control_if[j].end_of_packet[i];
      end
    end

    tbcm_round_robin_arbiter #(
      .REQUESTS     (5  ),
      .KEEP_RESULT  (1  )
    ) u_port_arbiter (
      .clk        (i_clk          ),
      .rst_n      (i_rst_n        ),
      .i_request  (port_request   ),
      .o_grant    (port_grant[i]  ),
      .i_free     (port_free      )
    );
  end

//--------------------------------------------------------------
//  VC Arbitration
//--------------------------------------------------------------
  logic [4:0][CHANNELS-1:0] vc_grant;
  logic [4:0][CHANNELS-1:0] vc_free;

  for (genvar i = 0;i < 5;++i) begin : g_vc_arbiter
    if (CHANNELS >= 2) begin : g
      logic [CHANNELS-1:0]  vc_request;

      for (genvar j = 0;j < CHANNELS;++j) begin : g
        always_comb begin
          vc_request[j] = port_grant[j][i] & port_control_if[i].request[j] & i_vc_ready[j];
          vc_free[i][j] = port_grant[j][i] & port_control_if[i].free[j];
        end
      end

      tbcm_round_robin_arbiter #(
        .REQUESTS     (CHANNELS ),
        .KEEP_RESULT  (1        )
      ) u_vc_arbiter (
        .clk        (i_clk        ),
        .rst_n      (i_rst_n      ),
        .i_request  (vc_request   ),
        .o_grant    (vc_grant[i]  ),
        .i_free     (vc_free[i]   )
      );
    end
    else begin : g
      always_comb begin
        vc_grant[i] = port_grant[0][i] & port_control_if[i].request;
        vc_free[i]  = port_grant[0][i] & port_control_if[i].free;
      end
    end
  end

//--------------------------------------------------------------
//  Grant
//--------------------------------------------------------------
  for (genvar i = 0;i < CHANNELS;++i) begin : g_grant
    logic [4:0] grant;
    logic [4:0] free;
    logic       fifo_full;
    logic       fifo_push;
    logic       fifo_pop;

    for (genvar j = 0;j < 5;++j) begin : g
      always_comb begin
        port_control_if[j].grant[i] = grant[j];
      end
    end

    always_comb begin
      for (int j = 0;j < 5;++j) begin
        grant[j]  = (!fifo_full) ? vc_grant[j][i] : '0;
        free[j]   = vc_free[j][i];
      end

      fifo_push = |free;
      fifo_pop  = i_output_free[i];
    end

    tbcm_fifo #(
      .WIDTH        (5  ),
      .DEPTH        (2  ),
      .DATA_FF_OUT  (1  ),
      .FLAG_FF_OUT  (1  )
    ) u_grant_fifo (
      .clk            (i_clk              ),
      .rst_n          (i_rst_n            ),
      .i_clear        ('0                 ),
      .o_empty        (),
      .o_almost_full  (),
      .o_full         (fifo_full          ),
      .i_push         (fifo_push          ),
      .i_data         (grant              ),
      .i_pop          (fifo_pop           ),
      .o_data         (o_output_grant[i]  )
    );
  end
endmodule

