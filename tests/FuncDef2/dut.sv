`ifndef TNOC_PKG_SV
`define TNOC_PKG_SV

`ifndef TNOC_DEFAULT_SIZE_X
  `define TNOC_DEFAULT_SIZE_X 3
`endif

`ifndef TNOC_DEFAULT_SIZE_Y
  `define TNOC_DEFAULT_SIZE_Y 3
`endif

`ifndef TNOC_DEFAULT_VIRTUAL_CHANNELS
  `define TNOC_DEFAULT_VIRTUAL_CHANNELS 2
`endif

`ifndef TNOC_DEFAULT_TAGS
  `define TNOC_DEFAULT_TAGS 256
`endif

`ifndef TNOC_DEFAULT_ADDRESS_WIDTH
  `define TNOC_DEFAULT_ADDRESS_WIDTH  64
`endif

`ifndef TNOC_DEFAULT_DATA_WIDTH
  `define TNOC_DEFAULT_DATA_WIDTH 256
`endif

`ifndef TNOC_DEFAULT_MAX_DATA_WIDTH
  `define TNOC_DEFAULT_MAX_DATA_WIDTH 256
`endif

`ifndef TNOC_DEFAULT_MAX_BYTE_LENGTH
  `define TNOC_DEFAULT_MAX_BYTE_LENGTH  4096
`endif

`ifndef TNOC_DEFAULT_FIFO_DEPTH
  `define TNOC_DEFAULT_FIFO_DEPTH 8
`endif

package tnoc_pkg;
//--------------------------------------------------------------
//  Configuration
//--------------------------------------------------------------
  typedef struct packed {
    shortint  size_x;
    shortint  size_y;
    shortint  virtual_channels;
    shortint  tags;
    shortint  address_width;
    shortint  data_width;
    shortint  max_data_width;
    shortint  max_byte_length;
  } tnoc_packet_config;

  localparam  tnoc_packet_config  TNOC_DEFAULT_PACKET_CONFIG  = '{
    size_x:           `TNOC_DEFAULT_SIZE_X,
    size_y:           `TNOC_DEFAULT_SIZE_Y,
    virtual_channels: `TNOC_DEFAULT_VIRTUAL_CHANNELS,
    tags:             `TNOC_DEFAULT_TAGS,
    address_width:    `TNOC_DEFAULT_ADDRESS_WIDTH,
    data_width:       `TNOC_DEFAULT_DATA_WIDTH,
    max_data_width:   `TNOC_DEFAULT_MAX_DATA_WIDTH,
    max_byte_length:  `TNOC_DEFAULT_MAX_BYTE_LENGTH
  };

  function automatic int tnoc_clog2(bit [31:0] n);
    int result;

    result  = 0;
    for (int i = 31;i >= 0;--i) begin
      if (n[i]) begin
        result  = i;
        break;
      end
    end

    if ((2**result) == n) begin
      return result;
    end
    else begin
      return result + 1;
    end
  endfunction

  function automatic int get_id_x_width(tnoc_packet_config packet_config);
    if (packet_config.size_x >= 2) begin
      return tnoc_clog2(packet_config.size_x);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_id_y_width(tnoc_packet_config packet_config);
    if (packet_config.size_y >= 2) begin
      return tnoc_clog2(packet_config.size_y);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_location_id_width(tnoc_packet_config packet_config);
    return get_id_x_width(packet_config) + get_id_y_width(packet_config);
  endfunction

  function automatic int get_vc_width(tnoc_packet_config packet_config);
    if (packet_config.virtual_channels >= 2) begin
      return tnoc_clog2(packet_config.virtual_channels);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_tag_width(tnoc_packet_config packet_config);
    if (packet_config.tags >= 2) begin
      return tnoc_clog2(packet_config.tags);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_byte_size_width(tnoc_packet_config packet_config);
    if (packet_config.max_data_width >= 16) begin
      return tnoc_clog2(tnoc_clog2(packet_config.max_data_width / 8) + 1);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_byte_length_width(tnoc_packet_config packet_config);
    return tnoc_clog2(packet_config.max_byte_length + 1);
  endfunction

  function automatic int get_packed_byte_length_width(tnoc_packet_config packet_config);
    if (packet_config.max_byte_length >= 2) begin
      return tnoc_clog2(packet_config.max_byte_length);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_byte_offset_width(tnoc_packet_config packet_config);
    if (packet_config.max_data_width >= 16) begin
      return tnoc_clog2(packet_config.max_data_width / 8);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_byte_end_width(tnoc_packet_config packet_config);
    if (packet_config.data_width >= 16) begin
      return tnoc_clog2(packet_config.data_width / 8);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_burst_length_width(tnoc_packet_config packet_config);
    int byte_width;
    byte_width  = packet_config.data_width / 8;
    return tnoc_clog2((packet_config.max_byte_length / byte_width) + 1);
  endfunction

//--------------------------------------------------------------
//  Packet
//--------------------------------------------------------------
  typedef enum logic [7:0] {
    TNOC_INVALID_PACKET     = 'b000_00000,
    TNOC_READ               = 'b001_00000,
    TNOC_WRITE              = 'b011_00000,
    TNOC_POSTED_WRITE       = 'b010_00000,
    TNOC_RESPONSE           = 'b100_00000,
    TNOC_RESPONSE_WITH_DATA = 'b110_00000
  } tnoc_packet_type;

  localparam  int TNOC_PACKET_TYPE_RESPONSE_BIT   = 7;
  localparam  int TNOC_PACKET_TYPE_PAYLOAD_BIT    = 6;
  localparam  int TNOC_PACKET_TYPE_NON_POSTED_BIT = 5;

  typedef enum logic [1:0] {
    TNOC_FIXED_BURST    = 2'b00,
    TNOC_NORMAL_BURST   = 2'b01,
    TNOC_WRAPPING_BURST = 2'b10
  } tnoc_burst_type;

  typedef struct packed {
    logic exokay;
    logic slave_error;
    logic decode_error;
  } tnoc_response_status;

  function automatic logic is_valid_packet_type(tnoc_packet_type packet_type);
    return (packet_type != TNOC_INVALID_PACKET);
  endfunction

  function automatic logic is_request_packet_type(tnoc_packet_type packet_type);
    return (is_valid_packet_type(packet_type) && (!packet_type[TNOC_PACKET_TYPE_RESPONSE_BIT]));
  endfunction

  function automatic logic is_response_packet_type(tnoc_packet_type packet_type);
    return (is_valid_packet_type(packet_type) && packet_type[TNOC_PACKET_TYPE_RESPONSE_BIT]);
  endfunction

  function automatic logic is_packet_with_payload_type(tnoc_packet_type packet_type);
    return (is_valid_packet_type(packet_type) && packet_type[TNOC_PACKET_TYPE_PAYLOAD_BIT]);
  endfunction

  function automatic logic is_header_only_packet_type(tnoc_packet_type packet_type);
    return (is_valid_packet_type(packet_type) && (!packet_type[TNOC_PACKET_TYPE_PAYLOAD_BIT]));
  endfunction

  function automatic logic is_posted_request_packet_type(tnoc_packet_type packet_type);
    return (is_request_packet_type(packet_type) && (!packet_type[TNOC_PACKET_TYPE_NON_POSTED_BIT]));
  endfunction

  function automatic logic is_non_posted_request_packet_type(tnoc_packet_type packet_type);
    return (is_request_packet_type(packet_type) && packet_type[TNOC_PACKET_TYPE_NON_POSTED_BIT]);
  endfunction

  function automatic int get_common_header_field_width(tnoc_packet_config packet_config);
    int width;
    width = 0;
    width += $bits(tnoc_packet_type);               //  packet type
    width += get_location_id_width(packet_config);  //  destination id
    width += get_location_id_width(packet_config);  //  source id
    width += get_vc_width(packet_config);           //  vc
    width += get_tag_width(packet_config);          //  tag
    width += 1;                                     //  invalid destination
    return width;
  endfunction

  function automatic int get_request_header_width(tnoc_packet_config packet_config);
    int width;
    width = 0;
    width += get_common_header_field_width(packet_config);  //  common fields
    width += get_byte_size_width(packet_config);            //  byte size
    width += get_packed_byte_length_width(packet_config);   //  byte length
    width += packet_config.address_width;                   //  address
    width += $bits(tnoc_burst_type);                        //  burst type
    return width;
  endfunction

  function automatic int get_response_header_width(tnoc_packet_config packet_config);
    int width;
    width = 0;
    width += get_common_header_field_width(packet_config);  //  common fields
    width += get_byte_size_width(packet_config);            //  byte size
    width += get_byte_offset_width(packet_config);          //  byte offset
    width += $bits(tnoc_response_status);                   //  status
    return width;
  endfunction

  function automatic int get_header_width(tnoc_packet_config packet_config);
    int width;

    width = 0;
    if (get_request_header_width(packet_config) > width) begin
      width = get_request_header_width(packet_config);
    end
    if (get_response_header_width(packet_config) > width) begin
      width = get_response_header_width(packet_config);
    end

    return width;
  endfunction

  function automatic int get_request_payload_width(tnoc_packet_config packet_config);
    int width;
    width = 0;
    width += packet_config.data_width;      //  data
    width += packet_config.data_width / 8;  //  byte enable
    return width;
  endfunction

  function automatic int get_response_payload_width(tnoc_packet_config packet_config);
    int width;
    width = 0;
    width += packet_config.data_width;          //  data
    width += $bits(tnoc_response_status);       //  status
    width += get_byte_end_width(packet_config); //  byte end
    width += 1;                                 //  last response
    return width;
  endfunction

  function automatic int get_payload_width(tnoc_packet_config packet_config);
    int width;

    width = 0;
    if (get_request_payload_width(packet_config) > width) begin
      width = get_request_payload_width(packet_config);
    end
    if (get_response_payload_width(packet_config) > width) begin
      width = get_response_payload_width(packet_config);
    end

    return width;
  endfunction

//--------------------------------------------------------------
//  Flit
//--------------------------------------------------------------
  typedef enum logic {
    TNOC_HEADER_FLIT  = 1'b0,
    TNOC_PAYLOAD_FLIT = 1'b1
  } tnoc_flit_type;

  function automatic int get_flit_data_width(tnoc_packet_config packet_config);
    int width;

    width = 0;
    if (get_common_header_field_width(packet_config) > width) begin
      width = get_common_header_field_width(packet_config);
    end
    if (get_payload_width(packet_config) > width) begin
      width = get_payload_width(packet_config);
    end

    return width;
  endfunction

  function automatic int get_flit_width(tnoc_packet_config packet_config);
    int width;

    width = 0;
    width += $bits(tnoc_flit_type);               //  flit_type
    width += 1;                                   //  head
    width += 1;                                   //  tail
    width += get_flit_data_width(packet_config);  //  data

    return width;
  endfunction

  function automatic int get_request_header_flits(tnoc_packet_config packet_config);
    int header_width;
    int flit_width;
    header_width  = get_request_header_width(packet_config);
    flit_width    = get_flit_data_width(packet_config);
    return (header_width + flit_width - 1) / flit_width;
  endfunction

  function automatic int get_response_header_flits(tnoc_packet_config packet_config);
    int header_width;
    int flit_width;
    header_width  = get_response_header_width(packet_config);
    flit_width    = get_flit_data_width(packet_config);
    return (header_width + flit_width - 1) / flit_width;
  endfunction

  function automatic int get_header_flits(tnoc_packet_config packet_config);
    int flits;

    flits = 0;
    if (get_request_header_flits(packet_config) > flits) begin
      flits = get_request_header_flits(packet_config);
    end
    if (get_response_header_flits(packet_config) > flits) begin
      flits = get_response_header_flits(packet_config);
    end

    return flits;
  endfunction

//--------------------------------------------------------------
//  ETC
//--------------------------------------------------------------
  typedef enum bit {
    TNOC_LOCAL_PORT     = 1'b0,
    TNOC_INTERNAL_PORT  = 1'b1
  } tnoc_port_type;

  function automatic bit is_local_port(tnoc_port_type port_type);
    return (port_type == TNOC_LOCAL_PORT);
  endfunction

  function automatic bit is_interna_port(tnoc_port_type port_type);
    return (port_type == TNOC_INTERNAL_PORT);
  endfunction

  function automatic int get_port_flit_width(
    tnoc_packet_config  packet_config,
    tnoc_port_type      port_type,
    int                 channels
  );
    int flit_width;
    flit_width  = get_flit_width(packet_config);
    if (is_local_port(port_type)) begin
      return channels * flit_width;
    end
    else begin
      return flit_width;
    end
  endfunction
endpackage
`endif


module tnoc_vc_splitter
  import  tnoc_pkg::*;
#(
  parameter   tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter   tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT,
  localparam  int                 CHANNELS      = PACKET_CONFIG.virtual_channels
)(
  tnoc_types            types,
  tnoc_flit_if.receiver receiver_if,
  tnoc_flit_if.sender   sender_if[CHANNELS]
);
  for (genvar i = 0;i < CHANNELS;++i) begin : g
    always_comb begin
      sender_if[i].valid      = receiver_if.valid[i];
      receiver_if.ready[i]    = sender_if[i].ready;
      receiver_if.vc_ready[i] = sender_if[i].vc_ready;
    end

    if (is_local_port(PORT_TYPE)) begin : g
      always_comb begin
        sender_if[i].flit = receiver_if.flit[i];
      end
    end
    else begin : g
      always_comb begin
        sender_if[i].flit = receiver_if.flit;
      end
    end
  end
endmodule
