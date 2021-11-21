module tnoc_flit_if_fifo
  import  tnoc_pkg::*;
#(
  parameter   tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter   int                 CHANNELS      = PACKET_CONFIG.virtual_channels,
  parameter   int                 DEPTH         = 8,
  parameter   int                 THRESHOLD     = DEPTH,
  parameter   bit                 DATA_FF_OUT   = 0,
  parameter   tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT,
  localparam  int                 FLITS         = (is_local_port(PORT_TYPE)) ? CHANNELS : 1
)(
  tnoc_types                    types,
  input   var logic             i_clk,
  input   var logic             i_rst_n,
  input   var logic             i_clear,
  output  var logic [FLITS-1:0] o_empty,
  output  var logic [FLITS-1:0] o_almost_full,
  output  var logic [FLITS-1:0] o_full,
  tnoc_flit_if.receiver         receiver_if,
  tnoc_flit_if.sender           sender_if
);
  localparam  int FLIT_WIDTH  = get_flit_width(PACKET_CONFIG);

  typedef struct packed {
    logic [CHANNELS-1:0]    valid;
    logic [FLIT_WIDTH-1:0]  flit;
  } fifo_data;

  logic [FLITS-1:0] empty;
  logic [FLITS-1:0] almost_full;
  logic [FLITS-1:0] full;

  assign  o_empty       = empty;
  assign  o_almost_full = almost_full;
  assign  o_full        = full;

  if (is_local_port(PORT_TYPE)) begin : g_local_port
    always_comb begin
      receiver_if.ready     = ~full;
      receiver_if.vc_ready  = ~almost_full;
    end

    always_comb begin
      sender_if.valid = ~empty;
    end

    for (genvar i = 0;i < CHANNELS;++i) begin : g
      tbcm_fifo #(
        .WIDTH        (FLIT_WIDTH   ),
        .THRESHOLD    (THRESHOLD    ),
        .FLAG_FF_OUT  (1            ),
        .DATA_FF_OUT  (DATA_FF_OUT  )
      ) u_fifo (
        .clk            (i_clk                ),
        .rst_n          (i_rst_n              ),
        .i_clear        (i_clear              ),
        .o_empty        (empty[i]             ),
        .o_almost_full  (almost_full[i]       ),
        .o_full         (full[i]              ),
        .i_push         (receiver_if.valid[i] ),
        .i_data         (receiver_if.flit[i]  ),
        .i_pop          (sender_if.ready[i]   ),
        .o_data         (sender_if.flit[i]    )
      );
    end
  end
  else if (CHANNELS >= 2) begin : g_multi_channels
    logic     push;
    fifo_data push_data;

    always_comb begin
      push                  = |receiver_if.valid;
      push_data.valid       = receiver_if.valid;
      push_data.flit        = receiver_if.flit[0];
      receiver_if.ready     = {CHANNELS{~full}};
      receiver_if.vc_ready  = {CHANNELS{~almost_full}};
    end

    logic     pop;
    fifo_data pop_data;

    always_comb begin
      sender_if.valid   = (!empty) ? pop_data.valid : '0;
      sender_if.flit[0] = pop_data.flit;
      pop               = |sender_if.get_ack();
    end

    tbcm_fifo #(
      .DATA_TYPE    (fifo_data    ),
      .DEPTH        (DEPTH        ),
      .THRESHOLD    (THRESHOLD    ),
      .FLAG_FF_OUT  (1            ),
      .DATA_FF_OUT  (DATA_FF_OUT  )
    ) u_fifo (
      .clk            (i_clk      ),
      .rst_n          (i_rst_n    ),
      .i_clear        (i_clear    ),
      .o_empty        (empty      ),
      .o_almost_full  (almost_full),
      .o_full         (full       ),
      .i_push         (push       ),
      .i_data         (push_data  ),
      .i_pop          (pop        ),
      .o_data         (pop_data   )
    );
  end
  else begin : g_single_channel
    always_comb begin
      receiver_if.ready     = ~full;
      receiver_if.vc_ready  = ~almost_full;
    end

    always_comb begin
      sender_if.valid = ~empty;
    end

    tbcm_fifo #(
      .WIDTH        (FLIT_WIDTH   ),
      .DEPTH        (DEPTH        ),
      .THRESHOLD    (THRESHOLD    ),
      .FLAG_FF_OUT  (1            ),
      .DATA_FF_OUT  (DATA_FF_OUT  )
    ) u_fifo (
      .clk            (i_clk              ),
      .rst_n          (i_rst_n            ),
      .i_clear        (i_clear            ),
      .o_empty        (empty              ),
      .o_almost_full  (almost_full        ),
      .o_full         (full               ),
      .i_push         (receiver_if.valid  ),
      .i_data         (receiver_if.flit   ),
      .i_pop          (sender_if.ready    ),
      .o_data         (sender_if.flit     )
    );
  end
endmodule
