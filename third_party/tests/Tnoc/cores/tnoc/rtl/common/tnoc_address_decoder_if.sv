`ifndef TNOC_ADDRESS_DECODER_IF_SV
`define TNOC_ADDRESS_DECODER_IF_SV
interface tnoc_address_decoder_if
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG
)(
  tnoc_types  types
);
  typedef types.tnoc_id_x                         tnoc_id_x;
  typedef types.tnoc_id_y                         tnoc_id_y;
  typedef logic [PACKET_CONFIG.address_width-1:0] tnoc_address;
  typedef types.tnoc_decode_result                tnoc_decode_result;

  tnoc_address  address;
  tnoc_id_x     id_x;
  tnoc_id_y     id_y;
  logic         decode_error;

  function automatic tnoc_decode_result decode(
    tnoc_address  request_address
  );
    tnoc_decode_result  result;
    address             = request_address;
    result.id.x         = id_x;
    result.id.y         = id_y;
    result.decode_error = decode_error;
    return result;
  endfunction

  modport requester (
    output  address,
    input   id_x,
    input   id_y,
    input   decode_error,
    import  decode
  );

  modport decoder (
    input   address,
    output  id_x,
    output  id_y,
    output  decode_error
  );

  modport monitor (
    input address,
    input id_x,
    input id_y,
    input decode_error
  );
endinterface
`endif
