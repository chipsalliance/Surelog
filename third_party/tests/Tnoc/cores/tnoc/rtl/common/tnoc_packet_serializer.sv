module tnoc_packet_serializer
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter int                 CHANNELS      = PACKET_CONFIG.virtual_channels,
  parameter tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT
)(
  tnoc_types            types,
  input var logic       i_clk,
  input var logic       i_rst_n,
  tnoc_packet_if.slave  packet_if,
  tnoc_flit_if.sender   sender_if
);
  typedef types.tnoc_vc         tnoc_vc;
  typedef types.tnoc_flit_data  tnoc_flit_data;

//--------------------------------------------------------------
//  Flit
//--------------------------------------------------------------
  tnoc_flit_if #(PACKET_CONFIG, 1)  flit_if[3](types);
  logic [1:0]                       select_flit;
  tnoc_flit_type                    current_flit_type;
  logic                             last_header_flit;
  logic                             header_only;

  always_comb begin
    select_flit[0]  = (current_flit_type == TNOC_HEADER_FLIT ) ? '1 : '0;
    select_flit[1]  = (current_flit_type == TNOC_PAYLOAD_FLIT) ? '1 : '0;
  end

  tnoc_flit_if_mux #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (1              ),
    .ENTRIES        (2              )
  ) u_flit_mux (
    .types        (types        ),
    .i_select     (select_flit  ),
    .receiver_if  (flit_if[0:1] ),
    .sender_if    (flit_if[2]   )
  );

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      current_flit_type <= TNOC_HEADER_FLIT;
    end
    else if (flit_if[2].get_channel_ack(0)) begin
      if (flit_if[2].flit[0].tail) begin
        current_flit_type <= TNOC_HEADER_FLIT;
      end
      else if (last_header_flit && (!header_only)) begin
        current_flit_type <= TNOC_PAYLOAD_FLIT;
      end
    end
  end

  if (CHANNELS == 1) begin : g_single_vc
    always_comb begin
      sender_if.valid   = flit_if[2].valid;
      flit_if[2].ready  = sender_if.ready;
      sender_if.flit    = flit_if[2].flit;
    end
  end
  else begin : g_multi_vc
    localparam  int FLITS = (is_local_port(PORT_TYPE)) ? CHANNELS : 1;

    tnoc_vc vc;
    tnoc_vc vc_latched;

    always_comb begin
      vc  = (
        current_flit_type == TNOC_HEADER_FLIT
      ) ? packet_if.header.vc : vc_latched;

      sender_if.valid     = '0;
      sender_if.valid[vc] = '1;
      flit_if[2].ready    = sender_if.ready[vc];
      for (int i = 0;i < FLITS;++i) begin
        sender_if.flit[i] = flit_if[2].flit;
      end
    end

    always_ff @(posedge i_clk) begin
      if (packet_if.get_header_ack()) begin
        vc_latched  <= packet_if.header.vc;
      end
    end
  end

//--------------------------------------------------------------
//  Header
//--------------------------------------------------------------
  localparam  int REQUEST_HEADER_FLITS  = get_request_header_flits(PACKET_CONFIG);
  localparam  int RESPONSE_HEADER_FLITS = get_response_header_flits(PACKET_CONFIG);
  localparam  int HEADER_FLITS          = get_header_flits(PACKET_CONFIG);

  always_comb begin
    header_only = is_header_only_packet_type(packet_if.header.packet_type);
  end

  if (HEADER_FLITS == 1) begin : g_single_header_flit
    always_comb begin
      last_header_flit        = '1;
      flit_if[0].valid        = packet_if.header_valid;
      packet_if.header_ready  = flit_if[0].ready;
      flit_if[0].flit[0]      = '{
        flit_type:  TNOC_HEADER_FLIT,
        head:       '1,
        tail:       header_only,
        data:       packet_if.pack_header()
      };
    end
  end
  else begin : g_multi_header_flits
    logic [$clog2(HEADER_FLITS)-1:0]    flit_count;
    tnoc_flit_data  [HEADER_FLITS-1:0]  packed_header;

    always_comb begin
      last_header_flit        = is_last_header_flit();
      packed_header           = packet_if.pack_header();
      flit_if[0].valid        = packet_if.header_valid;
      packet_if.header_ready  = (last_header_flit) ? flit_if[0].ready : '0;
      flit_if[0].flit[0]      = '{
        flit_type:  TNOC_HEADER_FLIT,
        head:       (flit_count == 0 ) ? 1'b1        : 1'b0,
        tail:       (last_header_flit) ? header_only : 1'b0,
        data:       packed_header[flit_count]
      };
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        flit_count  <= 0;
      end
      else if (flit_if[0].get_channel_ack(0)) begin
        flit_count  <=
          (last_header_flit) ? 0 : flit_count + 1;
      end
    end

    function automatic logic is_last_header_flit();
      tnoc_packet_type                  packet_type;
      logic [$clog2(HEADER_FLITS)-1:0]  last_flit_count;

      packet_type = packet_if.header.packet_type;
      if (is_request_packet_type(packet_type)) begin
        last_flit_count = REQUEST_HEADER_FLITS - 1;
      end
      else begin
        last_flit_count = RESPONSE_HEADER_FLITS - 1;
      end

      return (flit_count == last_flit_count) ? '1 : '0;
    endfunction
  end

//--------------------------------------------------------------
//  Payload
//--------------------------------------------------------------
  tnoc_packet_type  packet_type_latched;

  always_comb begin
    flit_if[1].valid        = packet_if.payload_valid;
    packet_if.payload_ready = flit_if[1].ready;
    flit_if[1].flit[0]      = '{
      flit_type:  TNOC_PAYLOAD_FLIT,
      head:       1'b0,
      tail:       packet_if.payload_last,
      data:       packet_if.pack_payload(packet_type_latched)
    };
  end

  always_ff @(posedge i_clk) begin
    if (packet_if.get_header_ack()) begin
      packet_type_latched <= packet_if.header.packet_type;
    end
  end
endmodule
