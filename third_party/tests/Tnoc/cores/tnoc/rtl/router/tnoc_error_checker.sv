module tnoc_error_checker
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config                  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter bit [PACKET_CONFIG.data_width-1:0]  ERROR_DATA    = '1
)(
  tnoc_types            types,
  input var logic       i_clk,
  input var logic       i_rst_n,
  tnoc_flit_if.receiver receiver_if,
  tnoc_flit_if.sender   sender_if
);
  typedef types.tnoc_common_header  tnoc_common_header;
  typedef types.tnoc_header_fields  tnoc_header_fields;
  typedef types.tnoc_byte_length    tnoc_byte_size;
  typedef types.tnoc_byte_length    tnoc_byte_length;
  typedef types.tnoc_address        tnoc_address;
  typedef types.tnoc_byte_offset    tnoc_byte_offset;
  typedef types.tnoc_byte_end       tnoc_byte_end;
  typedef types.tnoc_burst_length   tnoc_burst_length;

  localparam  tnoc_response_status  ERROR_STATUS  = '{
    exokay: 1'b0, slave_error: 1'b0, decode_error: 1'b1
  };

//--------------------------------------------------------------
//  Routing
//--------------------------------------------------------------
  typedef enum logic [1:0] {
    NORMAL_ROUTE  = 2'b01,
    ERROR_ROUTE   = 2'b10
  } e_route;

  e_route     route;
  e_route     route_latched;
  logic [1:0] error_route_busy;

  always_comb begin
    if (receiver_if.flit[0].head && (error_route_busy == '0)) begin
      route = (error_check()) ? ERROR_ROUTE : NORMAL_ROUTE;
    end
    else begin
      route = route_latched;
    end
  end

  always_ff @(posedge i_clk) begin
    if (receiver_if.get_head_flit_valid(0)) begin
      route_latched <= route;
    end
  end

  function automatic logic error_check();
    tnoc_common_header  header;
    header = tnoc_common_header'(receiver_if.flit[0].data);
    if (header.invalid_destination) begin
      return '1;
    end
    else if (header.destination_id.x >= PACKET_CONFIG.size_x) begin
      return '1;
    end
    else if (header.destination_id.y >= PACKET_CONFIG.size_y) begin
      return '1;
    end
    else begin
      return '0;
    end
  endfunction

  tnoc_flit_if #(PACKET_CONFIG, 1)  flit_if[5](types);

  tnoc_flit_if_demux #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (1              ),
    .ENTRIES        (2              )
  ) u_demux (
    .types        (types        ),
    .i_select     (route        ),
    .receiver_if  (receiver_if  ),
    .sender_if    (flit_if[0:1] )
  );

  tnoc_flit_if_mux #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (1              ),
    .ENTRIES        (2              )
  ) u_mux (
    .types        (types        ),
    .i_select     (route        ),
    .receiver_if  (flit_if[2:3] ),
    .sender_if    (flit_if[4]   )
  );

  tnoc_flit_if_slicer #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (1              ),
    .INTER_ROUTER   (0              )
  ) u_slicer (
    .types        (types      ),
    .i_clk        (i_clk      ),
    .i_rst_n      (i_rst_n    ),
    .receiver_if  (flit_if[4] ),
    .sender_if    (sender_if  )
  );

//--------------------------------------------------------------
//  Normal Route
//--------------------------------------------------------------
  tnoc_flit_if_connector u_normal_route (flit_if[0], flit_if[2]);

//--------------------------------------------------------------
//  Error Route
//--------------------------------------------------------------
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      error_route_busy[0] <= '0;
    end
    else if (flit_if[1].get_tail_flit_ack(0)) begin
      error_route_busy[0] <= '0;
    end
    else if (flit_if[1].get_head_flit_valid(0)) begin
      error_route_busy[0] <= '1;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      error_route_busy[1] <= '0;
    end
    else if (flit_if[3].get_tail_flit_ack(0)) begin
      error_route_busy[1] <= '0;
    end
    else if (flit_if[1].get_head_flit_valid(0)) begin
      error_route_busy[1] <= is_non_posted_request();
    end
  end

  function automatic logic is_non_posted_request();
    tnoc_common_header  header;
    header  = tnoc_common_header'(flit_if[1].flit[0].data);
    return is_non_posted_request_packet_type(header.packet_type);
  endfunction

  logic response_with_payload;

  always_ff @(posedge i_clk) begin
    if (flit_if[1].get_head_flit_valid(0)) begin
      response_with_payload <= is_response_with_payload();
    end
  end

  function automatic logic is_response_with_payload();
    tnoc_common_header  header;
    header  = tnoc_common_header'(flit_if[1].flit[0].data);
    return
      is_non_posted_request_packet_type(header.packet_type) &&
      is_header_only_packet_type(header.packet_type);
  endfunction

  tnoc_packet_if #(PACKET_CONFIG) error_packet_if[2](types);

  tnoc_packet_deserializer #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (1              )
  ) u_deserializer (
    .types        (types              ),
    .i_clk        (i_clk              ),
    .i_rst_n      (i_rst_n            ),
    .receiver_if  (flit_if[1]         ),
    .packet_if    (error_packet_if[0] )
  );

  always_comb begin
    if (error_route_busy == '0) begin
      error_packet_if[0].header_ready = '0;
    end
    else if (!error_route_busy[1]) begin
      error_packet_if[0].header_ready = '1;
    end
    else if (response_with_payload) begin
      error_packet_if[0].header_ready =
        (error_packet_if[1].payload_ready && error_packet_if[1].payload_last);
    end
    else begin
      error_packet_if[0].header_ready = '1;
    end
  end

  always_comb begin
    error_packet_if[0].payload_ready  = (
      error_route_busy[1] &&
      (!response_with_payload) &&
      error_packet_if[0].payload_last
    ) ? error_packet_if[1].header_ready : error_route_busy[0];
  end

  tnoc_header_fields  error_header_fields;
  tnoc_header_fields  error_header_fields_latched;

  always_comb begin
    error_header_fields =
      (error_packet_if[0].header_valid) ? error_packet_if[0].header : error_header_fields_latched;
  end

  always_ff @(posedge i_clk) begin
    if (error_packet_if[0].header_valid) begin
      error_header_fields_latched <= error_header_fields;
    end
  end

  tnoc_burst_length   burst_count;
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      burst_count <= 0;
    end
    else if (error_packet_if[1].get_payload_ack()) begin
      burst_count <=
        (error_packet_if[1].payload_last) ? 0 : burst_count + 1;
    end
  end

  tnoc_packet_type  response_packet_type;
  tnoc_byte_size    response_byte_size;
  tnoc_byte_offset  response_byte_offset;

  always_comb begin
    if (!error_route_busy[1]) begin
      error_packet_if[1].header_valid = '0;
    end
    else if (response_with_payload) begin
      error_packet_if[1].header_valid = error_packet_if[0].header_valid;
    end
    else begin
      error_packet_if[1].header_valid =
        (error_packet_if[0].payload_valid && error_packet_if[0].payload_last);
    end

    if (response_with_payload) begin
      response_packet_type  = TNOC_RESPONSE_WITH_DATA;
      response_byte_size    = error_header_fields.byte_size;
      response_byte_offset  = tnoc_byte_offset'(error_header_fields.address);
    end
    else begin
      response_packet_type  = TNOC_RESPONSE;
      response_byte_size    = '0;
      response_byte_offset  = '0;
    end

    error_packet_if[1].header = '{
      packet_type:          response_packet_type,
      destination_id:       error_header_fields.source_id,
      source_id:            error_header_fields.destination_id,
      vc:                   error_header_fields.vc,
      tag:                  error_header_fields.tag,
      invalid_destination:  '0,
      byte_size:            response_byte_size,
      byte_length:          '0,
      address:              '0,
      burst_type:           TNOC_NORMAL_BURST,
      byte_offset:          response_byte_offset,
      response_status:      ERROR_STATUS
    };
  end

  logic         last_response;
  tnoc_byte_end byte_end;

  always_comb begin
    last_response = get_last_response(error_header_fields, burst_count);
    byte_end      = get_byte_end(error_header_fields, last_response);

    error_packet_if[1].payload_valid  = (error_route_busy[1] && response_with_payload);
    error_packet_if[1].payload_last   = last_response;
    error_packet_if[1].payload        = '{
      data:             ERROR_DATA,
      byte_enable:      '0,
      response_status:  ERROR_STATUS,
      byte_end:         byte_end,
      last_response:    last_response
    };
  end

  tnoc_utils #(PACKET_CONFIG) u_utils(types);

  function automatic logic get_last_response(
    tnoc_header_fields  error_header_fields,
    tnoc_burst_length   burst_count
  );
    tnoc_byte_length  byte_length;
    tnoc_address      address;
    tnoc_burst_length burst_length;

    byte_length   = error_header_fields.byte_length;
    address       = error_header_fields.address;
    burst_length  = u_utils.calc_burst_length(byte_length, address);

    return ((burst_count + 1) == burst_length);
  endfunction

  function automatic tnoc_byte_end get_byte_end(
    tnoc_header_fields  error_header_fields,
    logic               last_response
  );
    if (last_response) begin
      tnoc_byte_length  byte_length;
      tnoc_address      address;
      byte_length = error_header_fields.byte_length;
      address     = error_header_fields.address;
      return tnoc_byte_end'(address) + tnoc_byte_end'(byte_length - 1);
    end
    else begin
      return '0;
    end
  endfunction

  tnoc_packet_serializer #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (1              )
  ) u_serializer (
    .types      (types              ),
    .i_clk      (i_clk              ),
    .i_rst_n    (i_rst_n            ),
    .packet_if  (error_packet_if[1] ),
    .sender_if  (flit_if[3]         )
  );
endmodule
