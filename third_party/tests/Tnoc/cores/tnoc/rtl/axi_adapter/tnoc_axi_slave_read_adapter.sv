module tnoc_axi_slave_read_adapter
  import  tnoc_pkg::*,
          tnoc_axi_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter tnoc_axi_config     AXI_CONFIG    = TNOC_DEFAULT_AXI_CONFIG,
  parameter int                 ID_X_WIDTH    = 1,
  parameter int                 ID_Y_WIDTH    = 1,
  parameter int                 VC_WIDTH      = 1
)(
  tnoc_types                        packet_types,
  tnoc_axi_types                    axi_types,
  input var logic                   i_clk,
  input var logic                   i_rst_n,
  input var logic [ID_X_WIDTH-1:0]  i_id_x,
  input var logic [ID_Y_WIDTH-1:0]  i_id_y,
  input var logic [VC_WIDTH-1:0]    i_base_vc,
  tnoc_address_decoder_if.requester decoder_if,
  tnoc_axi_if.slave_read            axi_if,
  tnoc_flit_if.receiver             receiver_if,
  tnoc_flit_if.sender               sender_if
);
  typedef packet_types.tnoc_decode_result tnoc_decode_result;
  typedef packet_types.tnoc_location_id   tnoc_location_id;
  typedef packet_types.tnoc_vc            tnoc_vc;
  typedef packet_types.tnoc_tag           tnoc_tag;
  typedef packet_types.tnoc_byte_size     tnoc_byte_size;
  typedef packet_types.tnoc_address       tnoc_address;
  typedef packet_types.tnoc_byte_length   tnoc_byte_length;
  typedef packet_types.tnoc_data          tnoc_data;
  typedef axi_types.tnoc_axi_id           tnoc_axi_id;
  typedef axi_types.tnoc_axi_data         tnoc_axi_data;

  tnoc_axi_utils #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .AXI_CONFIG     (AXI_CONFIG     )
  ) u_axi_utils (packet_types, axi_types);

//--------------------------------------------------------------
//  Request
//--------------------------------------------------------------
  tnoc_packet_if #(PACKET_CONFIG) request_if(packet_types);

  tnoc_decode_result  decode_result;
  tnoc_location_id    source_id;
  tnoc_address        address;
  tnoc_byte_length    byte_length;

  always_comb begin
    decode_result = decoder_if.decode(axi_if.araddr);
    source_id     = '{ x: i_id_x, y: i_id_y };
    address       = u_axi_utils.align_address(axi_if.araddr, axi_if.arsize);
    byte_length   = u_axi_utils.calc_byte_length(axi_if.arlen, axi_if.arsize);

    request_if.header_valid = axi_if.arvalid;
    axi_if.arready          = request_if.header_ready;
    request_if.header       = '{
      packet_type:          TNOC_READ,
      destination_id:       decode_result.id,
      source_id:            source_id,
      vc:                   u_axi_utils.get_vc(axi_if.arqos, i_base_vc),
      tag:                  tnoc_tag'(axi_if.arid),
      invalid_destination:  decode_result.decode_error,
      byte_size:            tnoc_byte_size'(axi_if.arsize),
      byte_length:          byte_length,
      address:              address,
      burst_type:           tnoc_burst_type'(axi_if.arburst),
      byte_offset:          '0,
      response_status:      '0
    };
  end

  always_comb begin
    request_if.payload_valid  = '0;
    request_if.payload_last   = '0;
    request_if.payload        = '0;
  end

  tnoc_packet_serializer #(
    .PACKET_CONFIG  (PACKET_CONFIG    ),
    .CHANNELS       (1                ),
    .PORT_TYPE      (TNOC_LOCAL_PORT  )
  ) u_serializer (
    .types      (packet_types ),
    .i_clk      (i_clk        ),
    .i_rst_n    (i_rst_n      ),
    .packet_if  (request_if   ),
    .sender_if  (sender_if    )
  );

//--------------------------------------------------------------
//  Response
//--------------------------------------------------------------
  tnoc_packet_if #(PACKET_CONFIG) response_if(packet_types);

  tnoc_packet_deserializer #(
    .PACKET_CONFIG  (PACKET_CONFIG    ),
    .CHANNELS       (1                ),
    .PORT_TYPE      (TNOC_LOCAL_PORT  )
  ) u_deserializer (
    .types        (packet_types ),
    .i_clk        (i_clk        ),
    .i_rst_n      (i_rst_n      ),
    .receiver_if  (receiver_if  ),
    .packet_if    (response_if  )
  );

  //  Header
  always_comb begin
    response_if.header_ready  = '1;
  end

  //  Payload
  localparam  int AXI_BYTE_WIDTH    = AXI_CONFIG.data_width / 8;
  localparam  int PACKET_BYTE_WIDTH = PACKET_CONFIG.data_width / 8;

  tnoc_axi_byte_counter #(
    .PACKET_CONFIG  (PACKET_CONFIG                        ),
    .AXI_CONFIG     (AXI_CONFIG                           ),
    .OFFSET_WIDTH   (get_byte_offset_width(PACKET_CONFIG) )
  ) u_byte_counter (i_clk, i_rst_n);

  always_comb begin
    u_byte_counter.initialize(
      response_if.get_header_ack(),
      response_if.header.byte_size, response_if.header.byte_offset
    );
  end

  always_comb begin
    u_byte_counter.up(
     axi_if.get_rchannel_ack(), response_if.get_payload_ack()
    );
  end

  logic                 rvalid;
  tnoc_axi_id           rid;
  tnoc_axi_data         rdata;
  logic                 rlast;
  logic                 payload_ready;
  tnoc_response_status  payload_status;
  logic                 payload_end;

  always_comb begin
    rvalid  = u_byte_counter.is_axi_ready();
  end

  always_comb begin
    if (payload_end) begin
      payload_ready = rvalid;
    end
    else begin
      payload_ready = u_byte_counter.is_packet_ready();
    end
  end

  always_comb begin
    if (rvalid) begin
      response_if.payload_ready = payload_ready && axi_if.rready;
    end
    else begin
      response_if.payload_ready = payload_ready;
    end
  end

  always_comb begin
    axi_if.rvalid = (rvalid) ? response_if.payload_valid : '0;
    axi_if.rid    = rid;
    axi_if.rdata  = rdata;
    axi_if.rresp  = convert_to_axi_status(payload_status);
    axi_if.rlast  = payload_end && response_if.payload.last_response;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      rid <= '0;
    end
    else if (response_if.get_header_ack()) begin
      rid <= tnoc_axi_id'(response_if.header.tag);
    end
  end

  always_comb begin
    payload_end =
      response_if.payload_last &&
        u_byte_counter.is_active_byte(response_if.payload.byte_end);
  end

  if (AXI_BYTE_WIDTH > PACKET_BYTE_WIDTH) begin : g_upsize
    localparam  int WORDS             = AXI_BYTE_WIDTH / PACKET_BYTE_WIDTH;
    localparam  int WORD_COUNT_WIDTH  = $clog2(WORDS);
    localparam  int WORD_COUNT_LSB    = $clog2(PACKET_BYTE_WIDTH);

    logic [WORD_COUNT_WIDTH-1:0]  word_count;

    always_comb begin
      word_count  =
        u_byte_counter.byte_count[WORD_COUNT_LSB+:WORD_COUNT_WIDTH];
    end

    tnoc_data [WORDS-1:0] payload_data;
    tnoc_response_status  status_latched;

    always_comb begin
      rdata           = payload_data;
      payload_status  = response_if.payload.response_status
                      | status_latched;
    end

    for (genvar i = 0;i < WORDS;++i) begin : g
      if (i < (WORDS - 1)) begin : g
        tnoc_data payload_data_latched;

        always_comb begin
          if (word_count == WORD_COUNT_WIDTH'(i)) begin
            payload_data[i] = response_if.payload.data;
          end
          else begin
            payload_data[i] = payload_data_latched;
          end
        end

        always_ff @(posedge i_clk) begin
          if (response_if.get_payload_ack()) begin
            payload_data_latched  <= payload_data[i];
          end
        end
      end
      else begin : g
        always_comb begin
          payload_data[i] = response_if.payload.data;
        end
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        status_latched  <= '0;
      end
      else if (axi_if.get_rchannel_ack()) begin
        status_latched  <= '0;
      end
      else if (response_if.get_payload_ack()) begin
        status_latched  <= payload_status;
      end
    end
  end
  else begin : g_downsize
    localparam  int WORDS             = PACKET_BYTE_WIDTH / AXI_BYTE_WIDTH;
    localparam  int WORD_COUNT_WIDTH  = (WORDS > 1) ? $clog2(WORDS) : 1;
    localparam  int WORD_COUNT_LSB    = $clog2(AXI_BYTE_WIDTH);

    logic [WORD_COUNT_WIDTH-1:0]  word_count;

    always_comb begin
      if (WORDS == 1) begin
        word_count  = WORD_COUNT_WIDTH'(0);
      end
      else begin
        word_count  =
          u_byte_counter.byte_count[WORD_COUNT_LSB+:WORD_COUNT_WIDTH];
      end
    end

    tnoc_axi_data [WORDS-1:0] payload_data;

    always_comb begin
      payload_data    = response_if.payload.data;
      payload_status  = response_if.payload.response_status;
      rdata           = payload_data[word_count];
    end
  end
endmodule
