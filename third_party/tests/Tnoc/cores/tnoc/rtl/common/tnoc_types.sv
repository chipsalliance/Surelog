`ifndef TNOC_TYPES_SV
`define TNOC_TYPES_SV
interface tnoc_types
  import  tnoc_pkg::*;
#(
  tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG
);
//--------------------------------------------------------------
//  Typedefs for packet
//--------------------------------------------------------------
  typedef logic [get_id_x_width(PACKET_CONFIG)-1:0]               tnoc_id_x;
  typedef logic [get_id_y_width(PACKET_CONFIG)-1:0]               tnoc_id_y;
  typedef logic [get_vc_width(PACKET_CONFIG)-1:0]                 tnoc_vc;
  typedef logic [get_tag_width(PACKET_CONFIG)-1:0]                tnoc_tag;
  typedef logic [get_byte_size_width(PACKET_CONFIG)-1:0]          tnoc_byte_size;
  typedef logic [get_byte_length_width(PACKET_CONFIG)-1:0]        tnoc_byte_length;
  typedef logic [get_packed_byte_length_width(PACKET_CONFIG)-1:0] tnoc_packed_byte_length;
  typedef logic [PACKET_CONFIG.address_width-1:0]                 tnoc_address;
  typedef logic [get_byte_offset_width(PACKET_CONFIG)-1:0]        tnoc_byte_offset;
  typedef logic [get_byte_end_width(PACKET_CONFIG)-1:0]           tnoc_byte_end;
  typedef logic [PACKET_CONFIG.data_width-1:0]                    tnoc_data;
  typedef logic [PACKET_CONFIG.data_width/8-1:0]                  tnoc_byte_enable;

  typedef struct packed {
    tnoc_id_x x;
    tnoc_id_y y;
  } tnoc_location_id;

  typedef struct packed {
    logic             invalid_destination;
    tnoc_tag          tag;
    tnoc_vc           vc;
    tnoc_location_id  source_id;
    tnoc_location_id  destination_id;
    tnoc_packet_type  packet_type;
  } tnoc_common_header_fields;

  typedef struct packed {
    tnoc_burst_type         burst_type;
    tnoc_address            address;
    tnoc_packed_byte_length byte_length;
    tnoc_byte_size          byte_size;
  } tnoc_request_header_fields;

  typedef struct packed {
    tnoc_response_status  response_status;
    tnoc_byte_offset      byte_offset;
    tnoc_byte_size        byte_size;
  } tnoc_response_header_fields;

  typedef tnoc_common_header_fields tnoc_common_header;

  typedef struct packed {
    tnoc_request_header_fields  request;
    tnoc_common_header_fields   common;
  } tnoc_request_header;

  typedef struct packed {
    tnoc_response_header_fields response;
    tnoc_common_header_fields   common;
  } tnoc_response_header;

  typedef struct packed {
    tnoc_byte_enable  byte_enable;
    tnoc_data         data;
  } tnoc_request_payload;

  typedef struct packed {
    logic                 last_response;
    tnoc_byte_end         byte_end;
    tnoc_response_status  response_status;
    tnoc_data             data;
  } tnoc_response_payload;

  typedef logic [get_header_width(PACKET_CONFIG)-1:0]   tnoc_packed_header;
  typedef logic [get_payload_width(PACKET_CONFIG)-1:0]  tnoc_packed_payload;

  typedef struct packed {
    tnoc_packet_type      packet_type;
    tnoc_location_id      destination_id;
    tnoc_location_id      source_id;
    tnoc_vc               vc;
    tnoc_tag              tag;
    logic                 invalid_destination;
    tnoc_byte_size        byte_size;
    tnoc_byte_length      byte_length;
    tnoc_address          address;
    tnoc_burst_type       burst_type;
    tnoc_byte_offset      byte_offset;
    tnoc_response_status  response_status;
  } tnoc_header_fields;

  typedef struct packed {
    tnoc_data             data;
    tnoc_byte_enable      byte_enable;
    tnoc_response_status  response_status;
    tnoc_byte_end         byte_end;
    logic                 last_response;
  } tnoc_payload_fields;

//--------------------------------------------------------------
//  Typedefs for Flit
//--------------------------------------------------------------
  typedef logic [get_flit_data_width(PACKET_CONFIG)-1:0]  tnoc_flit_data;

  typedef struct packed {
    tnoc_flit_data  data;
    logic           tail;
    logic           head;
    tnoc_flit_type  flit_type;
  } tnoc_flit;

//--------------------------------------------------------------
//  ETC
//--------------------------------------------------------------
  typedef logic [get_burst_length_width(PACKET_CONFIG)-1:0] tnoc_burst_length;

  typedef struct packed {
    tnoc_location_id  id;
    logic             decode_error;
  } tnoc_decode_result;
endinterface
`endif
