module tnoc_axi_slave_write_adapter
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
  tnoc_axi_if.slave_write           axi_if,
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
  typedef axi_types.tnoc_axi_id           tnoc_axi_id;

  tnoc_axi_utils #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .AXI_CONFIG     (AXI_CONFIG     )
  ) u_axi_utils (packet_types, axi_types);

//--------------------------------------------------------------
//  Request
//--------------------------------------------------------------
  tnoc_packet_if #(PACKET_CONFIG) request_if(packet_types);

  //  Header
  tnoc_decode_result  decode_result;
  tnoc_address        address;
  tnoc_byte_length    byte_length;

  always_comb begin
    decode_result = decoder_if.decode(axi_if.awaddr);
    address       = u_axi_utils.align_address(axi_if.awaddr, axi_if.awsize);
    byte_length   = u_axi_utils.calc_byte_length(axi_if.awlen, axi_if.awsize);

    request_if.header_valid = axi_if.awvalid;
    axi_if.awready          = request_if.header_ready;
    request_if.header       = '{
      packet_type:          TNOC_WRITE,
      destination_id:       decode_result.id,
      source_id:            '{ x: i_id_x, y: i_id_y },
      vc:                   u_axi_utils.get_vc(axi_if.awqos, i_base_vc),
      tag:                  tnoc_tag'(axi_if.awid),
      invalid_destination:  decode_result.decode_error,
      byte_size:            tnoc_byte_size'(axi_if.awsize),
      byte_length:          byte_length,
      address:              address,
      burst_type:           tnoc_burst_type'(axi_if.awburst),
      byte_offset:          '0,
      response_status:      '0
    };
  end

  logic header_done;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      header_done <= '0;
    end
    else if (request_if.get_payload_ack()) begin
      if (request_if.payload_last) begin
        header_done <= '0;
      end
    end
    else if (request_if.get_header_ack()) begin
      header_done <= '1;
    end
  end

  //  Payload
  localparam  int AXI_BYTE_WIDTH    = AXI_CONFIG.data_width / 8;
  localparam  int PACKET_BYTE_WIDTH = PACKET_CONFIG.data_width / 8;

  tnoc_axi_byte_counter #(
    .PACKET_CONFIG  (PACKET_CONFIG                ),
    .AXI_CONFIG     (AXI_CONFIG                   ),
    .OFFSET_WIDTH   (PACKET_CONFIG.address_width  )
  ) u_byte_counter (i_clk, i_rst_n);

  always_comb begin
    u_byte_counter.initialize(
      axi_if.get_awchannel_ack(),
      axi_if.awsize, address
    );
  end

  always_comb begin
    u_byte_counter.up(
      axi_if.get_wchannel_ack(), request_if.get_payload_ack()
    );
  end

  logic                               wready;
  logic [PACKET_BYTE_WIDTH-1:0][7:0]  axi_wdata;
  logic [PACKET_BYTE_WIDTH-1:0]       axi_wstrb;
  logic                               payload_valid;
  logic [PACKET_BYTE_WIDTH-1:0][7:0]  payload_data;
  logic [PACKET_BYTE_WIDTH-1:0]       payload_byte_enable;

  always_comb begin
    wready  = header_done && u_byte_counter.is_axi_ready();
  end

  always_comb begin
    payload_valid =
      header_done && ((axi_if.wlast && wready) || u_byte_counter.is_packet_ready());
  end

  always_comb begin
    if (payload_valid) begin
      axi_if.wready = wready && request_if.payload_ready;
    end
    else begin
      axi_if.wready = wready;
    end
  end

  always_comb begin
    request_if.payload_valid  = (payload_valid) ? axi_if.wvalid : '0;
    request_if.payload_last   = wready && axi_if.wlast;
    request_if.payload        = '{
      data:             payload_data,
      byte_enable:      payload_byte_enable,
      response_status:  '0,
      byte_end:         '0,
      last_response:    '0
    };
  end

  if (AXI_BYTE_WIDTH > PACKET_BYTE_WIDTH) begin : g_downsize
    localparam  int WORDS             = AXI_BYTE_WIDTH / PACKET_BYTE_WIDTH;
    localparam  int WORD_COUNT_WIDTH  = $clog2(WORDS);
    localparam  int WORD_COUNT_LSB    = $clog2(PACKET_BYTE_WIDTH);

    logic [WORD_COUNT_WIDTH-1:0]  word_count;

    always_comb begin
      word_count  = u_byte_counter.byte_count[WORD_COUNT_LSB+:WORD_COUNT_WIDTH];
      axi_wdata   = slice_wdata(axi_if.wdata, word_count);
      axi_wstrb   = slice_wstrb(axi_if.wstrb, word_count);
    end

    function automatic logic [PACKET_CONFIG.data_width-1:0] slice_wdata(
      logic [WORDS-1:0][PACKET_CONFIG.data_width-1:0] wdata,
      logic [WORD_COUNT_WIDTH-1:0]                    word_count
    );
      return wdata[word_count];
    endfunction

    function automatic logic [PACKET_CONFIG.data_width/8-1:0] slice_wstrb(
      logic [WORDS-1:0][PACKET_CONFIG.data_width/8-1:0] wstrb,
      logic [WORD_COUNT_WIDTH-1:0]                      word_count
    );
      return wstrb[word_count];
    endfunction
  end
  else begin : g_upsize
    localparam  int WORDS = PACKET_BYTE_WIDTH / AXI_BYTE_WIDTH;

    always_comb begin
      axi_wdata = {WORDS{axi_if.wdata}};
      axi_wstrb = {WORDS{axi_if.wstrb}};
    end
  end

  for (genvar i = 0;i < PACKET_BYTE_WIDTH;++i) begin : g_data
    if (i < (PACKET_BYTE_WIDTH - 1)) begin : g
      logic [7:0] data_latched;
      logic       byte_enable_latched;

      always_comb begin
        if (u_byte_counter.is_active_byte(i)) begin
          payload_data[i]         = axi_wdata[i];
          payload_byte_enable[i]  = axi_wstrb[i];
        end
        else begin
          payload_data[i]         = data_latched;
          payload_byte_enable[i]  = byte_enable_latched;
        end
      end

      always_ff @(posedge i_clk) begin
        data_latched  <= payload_data[i];
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          byte_enable_latched <= '0;
        end
        else if (request_if.get_payload_ack()) begin
          byte_enable_latched <= '0;
        end
        else begin
          byte_enable_latched <= payload_byte_enable[i];
        end
      end
    end
    else begin : g
      always_comb begin
        payload_data[i]         = axi_wdata[i];
        payload_byte_enable[i]  = (u_byte_counter.is_active_byte(i)) ? axi_wstrb[i] : '0;
      end
    end
  end

  //  Serialization
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

  always_comb begin
    axi_if.bvalid             = response_if.header_valid;
    response_if.header_ready  = axi_if.bready;
    axi_if.bid                = tnoc_axi_id'(response_if.header.tag);
    axi_if.bresp              = convert_to_axi_status(response_if.header.response_status);
  end

  always_comb begin
    response_if.payload_ready = '1;
  end
endmodule
