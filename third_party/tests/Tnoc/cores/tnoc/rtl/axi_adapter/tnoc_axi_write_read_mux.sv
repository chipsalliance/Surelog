module tnoc_axi_write_read_mux
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG
)(
  tnoc_types            types,
  input var logic       i_clk,
  input var logic       i_rst_n,
  tnoc_flit_if.receiver write_if,
  tnoc_flit_if.receiver read_if,
  tnoc_flit_if.sender   sender_if
);
  typedef types.tnoc_flit           tnoc_flit;
  typedef types.tnoc_common_header  tnoc_common_header;
  typedef types.tnoc_vc             tnoc_vc;

  localparam  int CHANNELS  = PACKET_CONFIG.virtual_channels;
  localparam  int VC_WIDTH  = get_vc_width(PACKET_CONFIG);

//--------------------------------------------------------------
//  VC Routing
//--------------------------------------------------------------
  tnoc_flit_if #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (1              )
  ) write_read_if[2*CHANNELS](types);

  tnoc_vc write_vc;
  tnoc_vc read_vc;
  tnoc_vc vc_latched[2];

  always_comb begin
    write_vc  = (
      write_if.flit[0].head
    ) ? get_vc_from_flit(write_if.flit[0]) : vc_latched[0];
    read_vc = (
      read_if.flit[0].head
    ) ? get_vc_from_flit(read_if.flit[0]) : vc_latched[1];
  end

  always_ff @(posedge i_clk) begin
    if (write_if.get_head_flit_valid(0)) begin
      vc_latched[0] <= write_vc;
    end
    if (read_if.get_head_flit_valid(0)) begin
      vc_latched[1] <= read_vc;
    end
  end

  function automatic tnoc_vc get_vc_from_flit(tnoc_flit flit);
    tnoc_common_header  header;
    header  = tnoc_common_header'(flit.data);
    return header.vc;
  endfunction

  logic [CHANNELS-1:0]  write_ready;
  logic [CHANNELS-1:0]  read_ready;

  always_comb begin
    write_if.ready    = |write_ready;
    write_if.vc_ready = '1;
    read_if.ready     = |read_ready;
    read_if.vc_ready  = '1;
  end

  for (genvar i = 0;i < CHANNELS;++i) begin : g_vc_routing
    localparam  bit [VC_WIDTH-1:0] VC = i;

    always_comb begin
      write_read_if[2*i+0].valid  = (write_vc == VC) ? write_if.valid             : '0;
      write_ready[i]              = (write_vc == VC) ? write_read_if[2*i+0].ready : '0;
      write_read_if[2*i+0].flit   = write_if.flit;
    end

    always_comb begin
      write_read_if[2*i+1].valid  = (read_vc == VC) ? read_if.valid              : '0;
      read_ready[i]               = (read_vc == VC) ? write_read_if[2*i+1].ready : '0;
      write_read_if[2*i+1].flit   = read_if.flit;
    end
  end

//--------------------------------------------------------------
//  Write/Read Arbitration
//--------------------------------------------------------------
  tnoc_types #(PACKET_CONFIG) types_temp();
  tnoc_flit_if #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (1              )
  ) vc_if[CHANNELS](types_temp);

  for (genvar i = 0;i < CHANNELS;++i) begin : g_arbiter
    logic [1:0] request;
    logic [1:0] grant;
    logic [1:0] free;

    always_comb begin
      request[0]  = write_read_if[2*i+0].get_head_flit_valid(0);
      free[0]     = write_read_if[2*i+0].get_tail_flit_ack(0);
      request[1]  = write_read_if[2*i+1].get_head_flit_valid(0);
      free[1]     = write_read_if[2*i+1].get_tail_flit_ack(0);
    end

    tbcm_round_robin_arbiter #(
      .REQUESTS     (2  ),
      .KEEP_RESULT  (1  )
    ) u_arbiter (
      .clk        (i_clk    ),
      .rst_n      (i_rst_n  ),
      .i_request  (request  ),
      .o_grant    (grant    ),
      .i_free     (free     )
    );

    tnoc_flit_if_mux #(
      .PACKET_CONFIG  (PACKET_CONFIG    ),
      .CHANNELS       (1                ),
      .ENTRIES        (2                ),
      .PORT_TYPE      (TNOC_LOCAL_PORT  )
    ) u_mux (
      .types        (types                    ),
      .i_select     (grant                    ),
      .receiver_if  (write_read_if[2*i:2*i+1] ),
      .sender_if    (vc_if[i]                 )
    );
  end

  tnoc_vc_mux #(
    .PACKET_CONFIG  (PACKET_CONFIG    ),
    .PORT_TYPE      (TNOC_LOCAL_PORT  )
  ) u_vc_mux (
    .types        (types      ),
    .i_vc_grant   ('0         ),
    .receiver_if  (vc_if      ),
    .sender_if    (sender_if  )
  );
endmodule
