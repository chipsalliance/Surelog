module tnoc_packet_deserializer
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter int                 CHANNELS      = PACKET_CONFIG.virtual_channels,
  parameter int                 FIFO_DEPTH    = 4,
  parameter tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT
)(
  tnoc_types            types,
  input var logic       i_clk,
  input var logic       i_rst_n,
  tnoc_flit_if.receiver receiver_if,
  tnoc_packet_if.master packet_if
);
  typedef types.tnoc_flit_data      tnoc_flit_data;
  typedef types.tnoc_common_header  tnoc_common_header;

//--------------------------------------------------------------
//  Flit
//--------------------------------------------------------------
  tnoc_flit_if #(PACKET_CONFIG, 1)  flit_if[3](types);

  if (CHANNELS == 1) begin : g_single_channel
    tnoc_flit_if_connector u_connector(receiver_if, flit_if[2]);
  end
  else begin : g_multi_channels
    tnoc_vc_arbiter #(
      .PACKET_CONFIG  (PACKET_CONFIG  ),
      .PORT_TYPE      (PORT_TYPE      ),
      .FIFO_DEPTH     (FIFO_DEPTH     )
    ) u_vc_arbiter (
      .types        (types        ),
      .i_clk        (i_clk        ),
      .i_rst_n      (i_rst_n      ),
      .receiver_if  (receiver_if  ),
      .sender_if    (flit_if[2]   )
    );
  end

  logic [1:0] select_flit;
  always_comb begin
    select_flit[0]  = (flit_if[2].flit[0].flit_type == TNOC_HEADER_FLIT ) ? '1 : '0;
    select_flit[1]  = (flit_if[2].flit[0].flit_type == TNOC_PAYLOAD_FLIT) ? '1 : '0;
  end

  tnoc_flit_if_demux #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (1              ),
    .ENTRIES        (2              )
  ) u_flit_if_demux (
    .types        (types        ),
    .i_select     (select_flit  ),
    .receiver_if  (flit_if[2]   ),
    .sender_if    (flit_if[0:1] )
  );

//--------------------------------------------------------------
//  Flit
//--------------------------------------------------------------
  localparam  int REQUEST_HEADER_FLITS  = get_request_header_flits(PACKET_CONFIG);
  localparam  int RESPONSE_HEADER_FLITS = get_response_header_flits(PACKET_CONFIG);
  localparam  int HEADER_FLITS          = get_header_flits(PACKET_CONFIG);

  if (HEADER_FLITS == 1) begin : g_single_header_flit
    always_comb begin
      packet_if.header_valid  = flit_if[0].valid;
      flit_if[0].ready        = packet_if.header_ready;
      packet_if.unpack_header(flit_if[0].flit[0].data);
    end
  end
  else begin : g_multi_header_flits
    logic [$clog2(HEADER_FLITS)-1:0]    flit_count;
    logic                               last_header_flit;
    tnoc_flit_data  [HEADER_FLITS-1:0]  header_flit_data;
    tnoc_flit_data                      header_flit_data_buffer[HEADER_FLITS-1];

    always_comb begin
      for (int i = 0;i < HEADER_FLITS;++i) begin
        if ((i == flit_count) || (i == (HEADER_FLITS - 1))) begin
          header_flit_data[i] = flit_if[0].flit[0].data;
        end
        else begin
          header_flit_data[i] = header_flit_data_buffer[i];
        end
      end

      last_header_flit        = is_last_header_flit();
      packet_if.header_valid  = (last_header_flit) ? flit_if[0].valid       : '0;
      flit_if[0].ready        = (last_header_flit) ? packet_if.header_ready : '1;
      packet_if.unpack_header(header_flit_data);
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

    always_ff @(posedge i_clk) begin
      if (flit_if[0].get_channel_ack(0) && (!last_header_flit)) begin
        header_flit_data_buffer[flit_count] <= flit_if[0].flit[0].data;
      end
    end

    function automatic logic is_last_header_flit();
      tnoc_common_header                common_header;
      logic [$clog2(HEADER_FLITS)-1:0]  last_count;

      common_header = tnoc_common_header'(header_flit_data[0]);
      if (is_request_packet_type(common_header.packet_type)) begin
        last_count  = REQUEST_HEADER_FLITS - 1;
      end
      else begin
        last_count  = RESPONSE_HEADER_FLITS - 1;
      end

      return (flit_count == last_count) ? '1 : '0;
    endfunction
  end

//--------------------------------------------------------------
//  Payload
//--------------------------------------------------------------
  always_comb begin
    packet_if.payload_valid = flit_if[1].valid;
    flit_if[1].ready        = packet_if.payload_ready;
    packet_if.payload_last  = flit_if[1].flit[0].tail;
    packet_if.unpack_payload(flit_if[1].flit[0].data);
  end
endmodule
