module tnoc_axi_master_write_adapter
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
  tnoc_axi_if.master_write          axi_if,
  tnoc_flit_if.receiver             receiver_if,
  tnoc_flit_if.sender               sender_if
);
  typedef struct packed {
    logic [get_id_x_width(PACKET_CONFIG)-1:0] source_x;
    logic [get_id_y_width(PACKET_CONFIG)-1:0] source_y;
    logic [AXI_CONFIG.qos_width-1:0]          qos;
    logic [get_tag_width(PACKET_CONFIG)-1:0]  tag;
  } tnoc_axi_request_info;

  typedef packet_types.tnoc_data        tnoc_data;
  typedef packet_types.tnoc_byte_enable tnoc_byte_enable;
  typedef packet_types.tnoc_byte_end    tnoc_byte_end;
  typedef axi_types.tnoc_axi_id         tnoc_axi_id;
  typedef axi_types.tnoc_axi_address    tnoc_axi_address;
  typedef axi_types.tnoc_axi_data       tnoc_axi_data;
  typedef axi_types.tnoc_axi_strobe     tnoc_axi_strobe;

  tnoc_axi_utils #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .AXI_CONFIG     (AXI_CONFIG     )
  ) u_utils (packet_types, axi_types);

//--------------------------------------------------------------
//  Request
//--------------------------------------------------------------
  tnoc_packet_if #(PACKET_CONFIG) request_if(packet_types);

  tnoc_packet_deserializer #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (1              )
  ) u_deserializer (
    .types        (packet_types ),
    .i_clk        (i_clk        ),
    .i_rst_n      (i_rst_n      ),
    .receiver_if  (receiver_if  ),
    .packet_if    (request_if   )
  );

  //  Header
  tnoc_axi_id_generator #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .AXI_CONFIG     (AXI_CONFIG     )
  ) u_id_generator (packet_types, axi_types);

  tnoc_axi_id_locker #(
    .AXI_CONFIG (AXI_CONFIG )
  ) u_id_locker (axi_types, i_clk, i_rst_n);

  logic awvalid;

  always_comb begin
    request_if.header_ready = '1;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      awvalid <= '0;
    end
    else if (axi_if.get_awchannel_ack()) begin
      awvalid <= '0;
    end
    else if (request_if.get_header_ack()) begin
      awvalid <= '1;
    end
  end

  always_comb begin
    axi_if.awvalid  =
      (!u_id_locker.is_locked(axi_if.awid)) ? awvalid : '0;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      axi_if.awid     <= '0;
      axi_if.awaddr   <= '0;
      axi_if.awlen    <= '0;
      axi_if.awsize   <= TNOC_AXI_BURST_SIZE_1_BYTE;
      axi_if.awburst  <= TNOC_AXI_FIXED_BURST;
      axi_if.awqos    <= '0;
    end
    else if (request_if.get_header_ack()) begin
      axi_if.awid     <= u_id_generator.get(request_if.header);
      axi_if.awaddr   <= tnoc_axi_address'(request_if.header.address);
      axi_if.awlen    <= u_utils.calc_burst_length(request_if.header);
      axi_if.awsize   <= u_utils.get_burst_size(request_if.header);
      axi_if.awburst  <= tnoc_axi_burst_type'(request_if.header.burst_type);
      axi_if.awqos    <= u_utils.get_qos(request_if.header.vc);
    end
  end

  always_comb begin
    u_id_locker.lock(axi_if.get_awchannel_ack(), axi_if.awid);
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
      request_if.get_header_ack(),
      u_utils.get_burst_size(request_if.header), request_if.header.address
    );
  end

  always_comb begin
    u_byte_counter.up(
     axi_if.get_wchannel_ack(), request_if.get_payload_ack()
    );
  end

  logic           payload_active;
  logic           payload_busy;
  logic           wvalid;
  tnoc_axi_data   wdata;
  tnoc_axi_strobe wstrb;
  logic           wlast;
  logic           payload_ready;
  logic           payload_last;
  tnoc_byte_end   byte_end;

  always_comb begin
    payload_active  = axi_if.get_awchannel_ack() || payload_busy;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      payload_busy  <= '0;
    end
    else if (axi_if.get_wchannel_ack() && axi_if.wlast) begin
      payload_busy  <= '0;
    end
    else if (axi_if.get_awchannel_ack()) begin
      payload_busy  <= '1;
    end
  end

  always_comb begin
    wvalid  = u_byte_counter.is_axi_ready() && payload_active;
  end

  always_comb begin
    axi_if.wvalid = wvalid && request_if.payload_valid;
    axi_if.wdata  = wdata;
    axi_if.wstrb  = wstrb;
    axi_if.wlast  = wlast;
  end

  always_comb begin
    wlast =
      request_if.payload_last &&
      u_byte_counter.is_active_byte(byte_end);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      byte_end  <= '0;
    end
    else if (request_if.get_header_ack()) begin
      byte_end  <=
        tnoc_byte_end'(request_if.header.address) +
        tnoc_byte_end'(request_if.header.byte_length) -
        tnoc_byte_end'(1);
    end
  end

  always_comb begin
    payload_ready =
      (wvalid && wlast) || (payload_active && u_byte_counter.is_packet_ready());
  end

  always_comb begin
    if (wvalid) begin
      request_if.payload_ready  = payload_ready && axi_if.wready;
    end
    else begin
      request_if.payload_ready  = payload_ready;
    end
  end

  if (AXI_BYTE_WIDTH > PACKET_BYTE_WIDTH) begin : g_upsize
    localparam  int WORDS               = AXI_BYTE_WIDTH / PACKET_BYTE_WIDTH;
    localparam  int WORD_COUNTER_WIDTH  = $clog2(WORDS);
    localparam  int WORD_COUNTER_LSB    = $clog2(PACKET_BYTE_WIDTH);

    logic [WORD_COUNTER_WIDTH-1:0]  word_count;

    always_comb begin
      word_count  =
        u_byte_counter.byte_count[WORD_COUNTER_LSB+:WORD_COUNTER_WIDTH];
    end

    tnoc_data [WORDS-1:0]         payload_data;
    tnoc_byte_enable  [WORDS-1:0] payload_byte_enable;

    always_comb begin
      wdata = payload_data;
      wstrb = payload_byte_enable;
    end

    for (genvar i = 0;i < WORDS;++i) begin : g
      if (i < (WORDS - 1)) begin : g
        tnoc_data         data_latched;
        tnoc_byte_enable  byte_enable_latched;

        always_comb begin
          if (word_count == WORD_COUNTER_WIDTH'(i)) begin
            payload_data[i]         = request_if.payload.data;
            payload_byte_enable[i]  = request_if.payload.byte_enable;
          end
          else begin
            payload_data[i]         = data_latched;
            payload_byte_enable[i]  = byte_enable_latched;
          end
        end

        always_ff @(posedge i_clk) begin
          if (request_if.get_payload_ack()) begin
            data_latched  <= payload_data[i];
          end
        end

        always_ff @(posedge i_clk, negedge i_rst_n) begin
          if (!i_rst_n) begin
            byte_enable_latched <= '0;
          end
          else if (axi_if.get_wchannel_ack()) begin
            byte_enable_latched <= '0;
          end
          else begin
            byte_enable_latched <= payload_byte_enable[i];
          end
        end
      end
      else begin : g
        always_comb begin
          payload_data[i] = request_if.payload.data;
          if (word_count == WORD_COUNTER_WIDTH'(i)) begin
            payload_byte_enable[i]  = request_if.payload.byte_enable;
          end
          else begin
            payload_byte_enable[i]  = '0;
          end
        end
      end
    end
  end
  else begin : g_downsize
    localparam  int WORDS               = PACKET_BYTE_WIDTH / AXI_BYTE_WIDTH;
    localparam  int WORD_COUNTER_WIDTH  = (WORDS > 1) ? $clog2(WORDS) : 1;
    localparam  int WORD_COUNTER_LSB    = $clog2(AXI_BYTE_WIDTH);

    logic [WORD_COUNTER_WIDTH-1:0]  word_count;

    always_comb begin
      if (WORDS == 1) begin
        word_count  = WORD_COUNTER_WIDTH'(0);
      end
      else begin
        word_count  =
          u_byte_counter.byte_count[WORD_COUNTER_LSB+:WORD_COUNTER_WIDTH];
      end
    end

    tnoc_axi_data [WORDS-1:0]   payload_data;
    tnoc_axi_strobe [WORDS-1:0] payload_byte_enable;

    always_comb begin
      payload_data        = request_if.payload.data;
      payload_byte_enable = request_if.payload.byte_enable;
      wdata               = payload_data[word_count];
      wstrb               = payload_byte_enable[word_count];
    end
  end

//--------------------------------------------------------------
//  Response
//--------------------------------------------------------------
  //  Request info buffer
  tnoc_axi_request_info request_info[2];

  always_ff @(posedge i_clk) begin
    if (request_if.get_header_ack()) begin
      request_info[0] <= '{
        source_x: request_if.header.source_id.x,
        source_y: request_if.header.source_id.y,
        qos:      u_utils.get_qos(request_if.header.vc),
        tag:      request_if.header.tag
      };
    end
  end

  tnoc_axi_request_info_buffer #(
    .AXI_CONFIG   (AXI_CONFIG             ),
    .REQUEST_INFO (tnoc_axi_request_info  ),
    .USE_UPDATE   (0                      )
  ) u_request_info_buffer (axi_types, i_clk, i_rst_n);

  always_comb begin
    u_request_info_buffer.initialize(
      axi_if.get_awchannel_ack(),
      axi_if.awid, request_info[0]
    );
  end

  //  Packet formation
  tnoc_packet_if #(PACKET_CONFIG) response_if(packet_types);

  always_comb begin
    request_info[1]           = u_request_info_buffer.get(axi_if.bid);
    response_if.header_valid  = axi_if.bvalid;
    axi_if.bready             = response_if.header_ready;
    response_if.header        = '{
      packet_type:          TNOC_RESPONSE,
      destination_id:       '{ x: request_info[1].source_x, y: request_info[1].source_y },
      source_id:            '{ x: i_id_x, y: i_id_y },
      vc:                   u_utils.get_vc(request_info[1].qos, i_base_vc),
      tag:                  request_info[1].tag,
      invalid_destination:  '0,
      byte_size:            '0,
      byte_length:          '0,
      address:              '0,
      burst_type:           TNOC_FIXED_BURST,
      byte_offset:          '0,
      response_status:      '0
    };
  end

  always_comb begin
    response_if.payload_valid = '0;
    response_if.payload_last  = '0;
    response_if.payload       = '0;
  end

  always_comb begin
    u_id_locker.free(axi_if.get_bchannel_ack(), axi_if.bid);
  end

  tnoc_packet_serializer #(
    .PACKET_CONFIG  (PACKET_CONFIG    ),
    .CHANNELS       (1                ),
    .PORT_TYPE      (TNOC_LOCAL_PORT  )
  ) u_serializer (
    .types      (packet_types ),
    .i_clk      (i_clk        ),
    .i_rst_n    (i_rst_n      ),
    .packet_if  (response_if  ),
    .sender_if  (sender_if    )
  );
endmodule
