module tnoc_port_contller_internal
  import  tnoc_pkg::*;
#(
  parameter int CHANNELS  = TNOC_DEFAULT_PACKET_CONFIG.virtual_channels
)(
  input   var logic                 i_clk,
  input   var logic                 i_rst_n,
  input   var logic [CHANNELS-1:0]  i_vc_ready,
  tnoc_port_control_if.controller   port_control_if[5],
  output  var logic [4:0]           o_output_grant,
  input   var logic                 i_output_free
);
  logic [CHANNELS-1:0][4:0] request;
  logic [CHANNELS-1:0][4:0] grant;
  logic [CHANNELS-1:0][4:0] free;

  for (genvar i = 0;i < CHANNELS;++i) begin : g_reorder
    for (genvar j = 0;j < 5;++j) begin : g
      always_comb begin
        request[i][j]               = port_control_if[j].request[i];
        port_control_if[j].grant[i] = grant[i][j];
        free[i][j]                  = port_control_if[j].free[i];
      end
    end
  end

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
    ) u_arbiter (
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
  logic [CHANNELS-1:0]  vc_grant;
  logic [CHANNELS-1:0]  vc_free;

  if (CHANNELS >= 2) begin : g_vc_arbtration
    logic [CHANNELS-1:0]  vc_request;

    always_comb begin
      for (int i = 0;i < CHANNELS;++i) begin
        vc_request[i] = |(request[i] & port_grant[i] & {5{i_vc_ready[i]}});
        vc_free[i]    = |(free[i]    & port_grant[i]);
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
  end
  else begin : g_vc_arbtration
    always_comb begin
      vc_grant  = |(request[0] & port_grant[0]);
      vc_free   = |(free[0]    & port_grant[0]);
    end
  end

//--------------------------------------------------------------
//  Grant
//--------------------------------------------------------------
  logic       fifo_full;
  logic       fifo_push;
  logic       fifo_pop;
  logic [4:0] output_grant;

  always_comb begin
    for (int i = 0;i < CHANNELS;++i) begin
      grant[i]  = (vc_grant[i] && (!fifo_full)) ? port_grant[i] : '0;
    end
  end

  tbcm_selector #(
    .WIDTH    (5        ),
    .ENTRIES  (CHANNELS ),
    .ONE_HOT  (1        )
  ) u_grant_selector();

  always_comb begin
    output_grant  = u_grant_selector.mux(vc_grant, port_grant);
  end

  always_comb begin
    fifo_push = |vc_free;
    fifo_pop  = i_output_free;
  end

  tbcm_fifo #(
    .WIDTH        (5  ),
    .DEPTH        (2  ),
    .DATA_FF_OUT  (1  ),
    .FLAG_FF_OUT  (1  )
  ) u_grant_fifo (
    .clk            (i_clk          ),
    .rst_n          (i_rst_n        ),
    .i_clear        ('0             ),
    .o_empty        (),
    .o_almost_full  (),
    .o_full         (fifo_full      ),
    .i_push         (fifo_push      ),
    .i_data         (output_grant   ),
    .i_pop          (fifo_pop       ),
    .o_data         (o_output_grant )
  );
endmodule
