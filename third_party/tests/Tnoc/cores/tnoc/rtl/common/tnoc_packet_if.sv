`ifndef TNOC_PACKET_IF_SV
`define TNOC_PACKET_IF_SV
interface tnoc_packet_if
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG
)(
  tnoc_types  types
);
//--------------------------------------------------------------
//  Variable declarations
//--------------------------------------------------------------
  typedef types.tnoc_header_fields  tnoc_header_fields;
  typedef types.tnoc_payload_fields tnoc_payload_fields;

  logic               header_valid;
  logic               header_ready;
  tnoc_header_fields  header;
  logic               payload_valid;
  logic               payload_ready;
  logic               payload_last;
  tnoc_payload_fields payload;

//--------------------------------------------------------------
//  API
//--------------------------------------------------------------
  function automatic logic get_header_ack();
    return header_valid & header_ready;
  endfunction

  function automatic logic get_payload_ack();
    return payload_valid & payload_ready;
  endfunction

  typedef types.tnoc_byte_length            tnoc_byte_length;
  typedef types.tnoc_packed_byte_length     tnoc_packed_byte_length;
  typedef types.tnoc_common_header_fields   tnoc_common_header_fields;
  typedef types.tnoc_request_header_fields  tnoc_request_header_fields;
  typedef types.tnoc_response_header_fields tnoc_response_header_fields;
  typedef types.tnoc_common_header          tnoc_common_header;
  typedef types.tnoc_request_header         tnoc_request_header;
  typedef types.tnoc_response_header        tnoc_response_header;
  typedef types.tnoc_packed_header          tnoc_packed_header;

  function automatic logic [get_header_width(PACKET_CONFIG)-1:0] pack_header();
    tnoc_common_header_fields common_fields;

    common_fields.packet_type         = header.packet_type;
    common_fields.destination_id      = header.destination_id;
    common_fields.source_id           = header.source_id;
    common_fields.vc                  = header.vc;
    common_fields.tag                 = header.tag;
    common_fields.invalid_destination = header.invalid_destination;

    if (header.packet_type[TNOC_PACKET_TYPE_RESPONSE_BIT]) begin
      tnoc_response_header_fields response_fields;
      tnoc_response_header        response_header;

      response_fields.byte_size       = header.byte_size;
      response_fields.byte_offset     = header.byte_offset;
      response_fields.response_status = header.response_status;

      response_header.common    = common_fields;
      response_header.response  = response_fields;
      return tnoc_packed_header'(response_header);
    end
    else begin
      tnoc_request_header_fields  request_fields;
      tnoc_request_header         request_header;

      request_fields.byte_size    = header.byte_size;
      request_fields.byte_length  = tnoc_packed_byte_length'(header.byte_length);
      request_fields.address      = header.address;
      request_fields.burst_type   = header.burst_type;

      request_header.common   = common_fields;
      request_header.request  = request_fields;
      return tnoc_packed_header'(request_header);
    end
  endfunction

  function automatic void unpack_header(tnoc_packed_header packed_header);
    tnoc_byte_length      byte_length;
    tnoc_common_header    common_header;
    tnoc_request_header   request_header;
    tnoc_response_header  response_header;

    common_header   = tnoc_common_header'(packed_header);
    request_header  = tnoc_request_header'(packed_header);
    response_header = tnoc_response_header'(packed_header);

    byte_length = {
      ((request_header.request.byte_length == '0) ? 1'b1 : 1'b0),
      request_header.request.byte_length
    };

    header.packet_type          = common_header.packet_type;
    header.destination_id       = common_header.destination_id;
    header.source_id            = common_header.source_id;
    header.vc                   = common_header.vc;
    header.tag                  = common_header.tag;
    header.invalid_destination  = common_header.invalid_destination;
    header.byte_size            = request_header.request.byte_size;
    header.byte_length          = byte_length;
    header.address              = request_header.request.address;
    header.burst_type           = request_header.request.burst_type;
    header.byte_offset          = response_header.response.byte_offset;
    header.response_status      = response_header.response.response_status;
  endfunction

  typedef types.tnoc_request_payload    tnoc_request_payload;
  typedef types.tnoc_response_payload   tnoc_response_payload;
  typedef types.tnoc_packed_payload     tnoc_packed_payload;

  function automatic logic [get_payload_width(PACKET_CONFIG)-1:0] pack_payload(tnoc_packet_type packet_type);
    if (packet_type[TNOC_PACKET_TYPE_RESPONSE_BIT]) begin
      tnoc_response_payload response_payload;
      response_payload.data             = payload.data;
      response_payload.response_status  = payload.response_status;
      response_payload.byte_end         = payload.byte_end;
      response_payload.last_response    = payload.last_response;
      return tnoc_packed_payload'(response_payload);
    end
    else begin
      tnoc_request_payload  request_payload;
      request_payload.data        = payload.data;
      request_payload.byte_enable = payload.byte_enable;
      return tnoc_packed_payload'(request_payload);
    end
  endfunction

  function automatic void unpack_payload(tnoc_packed_payload packed_payload);
    tnoc_request_payload  request_payload;
    tnoc_response_payload response_payload;

    request_payload   = tnoc_request_payload'(packed_payload);
    response_payload  = tnoc_response_payload'(packed_payload);

    payload.data            = request_payload.data;
    payload.byte_enable     = request_payload.byte_enable;
    payload.response_status = response_payload.response_status;
    payload.byte_end        = response_payload.byte_end;
    payload.last_response   = response_payload.last_response;
  endfunction

//--------------------------------------------------------------
//  Modport
//--------------------------------------------------------------
  modport master (
    output  header_valid,
    input   header_ready,
    output  header,
    output  payload_valid,
    input   payload_ready,
    output  payload_last,
    output  payload,
    import  get_header_ack,
    import  get_payload_ack,
    import  unpack_header,
    import  unpack_payload
  );

  modport slave (
    input   header_valid,
    output  header_ready,
    input   header,
    input   payload_valid,
    output  payload_ready,
    input   payload_last,
    input   payload,
    import  get_header_ack,
    import  get_payload_ack,
    import  pack_header,
    import  pack_payload
  );

  modport monitor (
    input   header_valid,
    input   header_ready,
    input   header,
    input   payload_valid,
    input   payload_ready,
    input   payload_last,
    import  get_header_ack,
    import  get_payload_ack
  );
endinterface
`endif
