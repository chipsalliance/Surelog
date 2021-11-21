module tnoc_axi_master_read_adapter
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
  tnoc_axi_if.master_read           axi_if,
  tnoc_flit_if.receiver             receiver_if,
  tnoc_flit_if.sender               sender_if
);
  typedef struct packed {
    logic [get_id_x_width(PACKET_CONFIG)-1:0]         source_x;
    logic [get_id_y_width(PACKET_CONFIG)-1:0]         source_y;
    logic [AXI_CONFIG.qos_width-1:0]                  qos;
    logic [get_tag_width(PACKET_CONFIG)-1:0]          tag;
    logic [get_byte_size_width(PACKET_CONFIG)-1:0]    byte_size;
    logic [get_byte_offset_width(PACKET_CONFIG)-1:0]  byte_offset;
  } tnoc_axi_request_info;

  typedef packet_types.tnoc_data        tnoc_data;
  typedef packet_types.tnoc_byte_offset tnoc_byte_offset;
  typedef packet_types.tnoc_byte_end    tnoc_byte_end;
  typedef axi_types.tnoc_axi_id         tnoc_axi_id;
  typedef axi_types.tnoc_axi_address    tnoc_axi_address;
  typedef axi_types.tnoc_axi_data       tnoc_axi_data;

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

  tnoc_axi_id_generator #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .AXI_CONFIG     (AXI_CONFIG     )
  ) u_id_generator (packet_types, axi_types);

  tnoc_axi_id_locker #(
    .AXI_CONFIG (AXI_CONFIG )
  ) u_id_locker (axi_types, i_clk, i_rst_n);

  logic arvalid;

  always_comb begin
    if (arvalid) begin
      request_if.header_ready = axi_if.get_archannel_ack();
    end
    else begin
      request_if.header_ready = '1;
    end
  end

  always_comb begin
    request_if.payload_ready  = '0;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      arvalid <= '0;
    end
    else if (request_if.get_header_ack()) begin
      arvalid <= '1;
    end
    else if (axi_if.get_archannel_ack()) begin
      arvalid <= '0;
    end
  end

  always_comb begin
    axi_if.arvalid  =
      (!u_id_locker.is_locked(axi_if.arid)) ? arvalid : '0;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      axi_if.arid     <= '0;
      axi_if.araddr   <= '0;
      axi_if.arlen    <= '0;
      axi_if.arsize   <= TNOC_AXI_BURST_SIZE_1_BYTE;
      axi_if.arburst  <= TNOC_AXI_FIXED_BURST;
      axi_if.arqos    <= '0;
    end
    else if (request_if.get_header_ack()) begin
      axi_if.arid     <= u_id_generator.get(request_if.header);
      axi_if.araddr   <= tnoc_axi_address'(request_if.header.address);
      axi_if.arlen    <= u_utils.calc_burst_length(request_if.header);
      axi_if.arsize   <= u_utils.get_burst_size(request_if.header);
      axi_if.arburst  <= tnoc_axi_burst_type'(request_if.header.burst_type);
      axi_if.arqos    <= u_utils.get_qos(request_if.header.vc);
    end
  end

  always_comb begin
    u_id_locker.lock(axi_if.get_archannel_ack(), axi_if.arid);
  end

//--------------------------------------------------------------
//  Response
//--------------------------------------------------------------
  localparam  int PACKET_BYTE_SIZE    = PACKET_CONFIG.data_width / 8;
  localparam  int AXI_BYTE_SIZE       = AXI_CONFIG.data_width / 8;
  localparam  int AXI_BYTE_SIZE_WIDTH = $clog2($clog2(AXI_BYTE_SIZE) + 1);

  tnoc_packet_if #(PACKET_CONFIG) response_if(packet_types);

  logic                 axi_ready;
  logic                 packet_ready;
  logic                 rvalid;
  tnoc_axi_id           rid;
  tnoc_axi_data         rdata;
  tnoc_axi_response     rresp;
  logic                 rlast;
  logic                 next_packet;
  tnoc_axi_request_info request_info[4];
  logic                 update_request_info;
  logic                 header_done;
  logic                 payload_valid;
  logic                 payload_last;
  logic                 payload_last_valid;
  tnoc_data             payload_data;
  tnoc_response_status  payload_status;
  tnoc_response_status  payload_status_latched;
  tnoc_byte_end         payload_byte_end;
  tnoc_data             axi_rdata;

  always_comb begin
    axi_ready     = header_done && u_byte_counter.is_axi_ready();
    packet_ready  = header_done && u_byte_counter.is_packet_ready();
  end

  //  Input buffering
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      rvalid  <= '0;
    end
    else if (rvalid && axi_if.rready && rlast) begin
      rvalid  <= axi_if.rvalid;
    end
    else if (!rvalid) begin
      rvalid  <= axi_if.rvalid;
    end
  end

  always_comb begin
    if (!rvalid) begin
      axi_if.rready = '1;
    end
    else if (packet_ready || payload_last) begin
      axi_if.rready = axi_ready && response_if.get_payload_ack();
    end
    else begin
      axi_if.rready = axi_ready;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      rid <= '0;
    end
    else if (axi_if.get_rchannel_ack()) begin
      rid <= axi_if.rid;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      rlast <= '0;
    end
    else if (axi_if.get_rchannel_ack()) begin
      rlast <= axi_if.rlast;
    end
    else if (rvalid && axi_if.rready && rlast) begin
      rlast <= '0;
    end
  end

  always_ff @(posedge i_clk) begin
    if (axi_if.get_rchannel_ack()) begin
      rdata <= axi_if.rdata;
      rresp <= axi_if.rresp;
    end
  end

  always_comb begin
    u_id_locker.free(rvalid && axi_if.rready && rlast, rid);
  end

  always_comb begin
    next_packet = rvalid && axi_if.rvalid && (rid != axi_if.rid);
  end

  //  Request info buffer
  tnoc_axi_request_info_buffer #(
    .AXI_CONFIG   (AXI_CONFIG             ),
    .REQUEST_INFO (tnoc_axi_request_info  ),
    .USE_UPDATE   (1                      )
  ) u_request_info_buffer (axi_types, i_clk, i_rst_n);

  always_ff @(posedge i_clk) begin
    if (request_if.get_header_ack()) begin
      request_info[0] <= '{
        source_x:     request_if.header.source_id.x,
        source_y:     request_if.header.source_id.y,
        qos:          u_utils.get_qos(request_if.header.vc),
        tag:          request_if.header.tag,
        byte_size:    request_if.header.byte_size,
        byte_offset:  tnoc_byte_offset'(request_if.header.address)
      };
    end
  end

  always_comb begin
    u_request_info_buffer.initialize(
      axi_if.get_archannel_ack(),
      axi_if.arid, request_info[0]
    );
  end

  always_ff @(posedge i_clk) begin
    if (axi_if.get_rchannel_ack()) begin
      request_info[1] = u_request_info_buffer.get(axi_if.rid);
    end
  end

  always_ff @(posedge i_clk) begin
    if (axi_if.get_rchannel_ack()) begin
      if ((!rvalid) || next_packet) begin
        request_info[2] <= request_info[1];
      end
    end
  end

  always_comb begin
    update_request_info = axi_if.get_rchannel_ack() && next_packet;
    request_info[3]     = '{
      source_x:     request_info[2].source_x,
      source_y:     request_info[2].source_y,
      qos:          request_info[2].qos,
      tag:          request_info[2].tag,
      byte_size:    request_info[2].byte_size,
      byte_offset:  tnoc_byte_offset'(u_byte_counter.byte_count_next)
    };
    u_request_info_buffer.update(
      update_request_info, rid, request_info[3]
    );
  end

  //  Byte counter
  tnoc_axi_byte_counter #(
    .PACKET_CONFIG  (PACKET_CONFIG                        ),
    .AXI_CONFIG     (AXI_CONFIG                           ),
    .OFFSET_WIDTH   (get_byte_offset_width(PACKET_CONFIG) )
  ) u_byte_counter (i_clk, i_rst_n);

  always_comb begin
    u_byte_counter.initialize(
      response_if.get_header_ack(),
      u_utils.clip_burst_size(request_info[2].byte_size),
      request_info[2].byte_offset
    );
  end

  always_comb begin
    u_byte_counter.up(
      rvalid && axi_if.get_rchannel_ack(), response_if.get_payload_ack()
    );
  end

  //  Header
  always_comb begin
    response_if.header_valid  = (!header_done) ? rvalid : '0;
    response_if.header        = '{
      packet_type:          TNOC_RESPONSE_WITH_DATA,
      destination_id:       '{ x: request_info[1].source_x, y: request_info[1].source_y },
      source_id:            '{ x: i_id_x, y: i_id_y },
      vc:                   u_utils.get_vc(request_info[1].qos, i_base_vc),
      tag:                  request_info[1].tag,
      invalid_destination:  '0,
      byte_size:            request_info[1].byte_size,
      byte_length:          '0,
      address:              '0,
      burst_type:           TNOC_FIXED_BURST,
      byte_offset:          request_info[1].byte_offset,
      response_status:      '0
    };
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      header_done <= '0;
    end
    else if (response_if.get_payload_ack()) begin
      if (response_if.payload_last) begin
        header_done <= '0;
      end
    end
    else if (response_if.get_header_ack()) begin
      header_done <= '1;
    end
  end

  //  Payload
  localparam  bit [AXI_BYTE_SIZE_WIDTH-1:0] PACKET_MAX_BYTE_SIZE  = $clog2(PACKET_BYTE_SIZE);

  always_comb begin
    payload_last        = rlast || next_packet;
    payload_last_valid  = (u_byte_counter.byte_size > PACKET_MAX_BYTE_SIZE)
                            ? payload_last && packet_ready
                            : payload_last && axi_ready;
    payload_valid       = (rvalid && axi_if.rvalid && packet_ready) || payload_last_valid;
  end

  always_comb begin
    payload_byte_end          = tnoc_byte_end'(u_byte_counter.byte_count_next - 1);
    response_if.payload_valid = payload_valid;
    response_if.payload_last  = payload_last && axi_ready;
    response_if.payload       = '{
      data:             payload_data,
      byte_enable:      '0,
      response_status:  payload_status,
      byte_end:         (response_if.payload_last) ? payload_byte_end : '0,
      last_response:    (response_if.payload_last) ? rlast            : '0
    };
  end

  if (PACKET_BYTE_SIZE < AXI_BYTE_SIZE) begin : g_downsize
    localparam  int WORDS             = AXI_BYTE_SIZE / PACKET_BYTE_SIZE;
    localparam  int WORD_COUNT_WIDTH  = $clog2(WORDS);
    localparam  int WORD_COUNT_LSB    = $clog2(PACKET_BYTE_SIZE);

    logic [WORD_COUNT_WIDTH-1:0]  word_count;

    always_comb begin
      word_count  = u_byte_counter.byte_count[WORD_COUNT_LSB+:WORD_COUNT_WIDTH];
      axi_rdata   = slice_rdata(rdata, word_count);
    end

    function automatic tnoc_data slice_rdata(
      tnoc_data [WORDS-1:0]         rdata,
      logic [WORD_COUNT_WIDTH-1:0]  word_count
    );
      return rdata[word_count];
    endfunction
  end
  else begin : g_upsize
    localparam  int WORDS = PACKET_BYTE_SIZE / AXI_BYTE_SIZE;

    always_comb begin
      axi_rdata = {WORDS{rdata}};
    end
  end

  for (genvar i = 0;i < PACKET_BYTE_SIZE;++i) begin : g_data
    if (i < (PACKET_BYTE_SIZE - 1)) begin : g
      logic [7:0] data_latched;

      always_comb begin
        if (u_byte_counter.is_active_byte(i)) begin
          payload_data[8*i+:8]  = axi_rdata[8*i+:8];
        end
        else begin
          payload_data[8*i+:8]  = data_latched;
        end
      end

      always_ff @(posedge i_clk) begin
        data_latched  <= payload_data[8*i+:8];
      end
    end
    else begin : g
      always_comb begin
        payload_data[8*i+:8]  = axi_rdata[8*i+:8];
      end
    end
  end

  always_comb begin
    payload_status  = convert_from_axi_status(rresp)
                    | payload_status_latched;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      payload_status_latched  <= '0;
    end
    else if (response_if.get_payload_ack()) begin
      payload_status_latched  <= '0;
    end
    else if (rvalid && axi_if.get_rchannel_ack()) begin
      payload_status_latched  <= payload_status;
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
    .packet_if  (response_if  ),
    .sender_if  (sender_if    )
  );
endmodule
