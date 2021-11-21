`ifndef TNOC_BFM_UTILS_SVH
`define TNOC_BFM_UTILS_SVH

function automatic bit is_response_packet(tnoc_bfm_packet_type packet_type);
  return packet_type[TNOC_BFM_RESPONSE_BIT];
endfunction

function automatic bit is_request_packet(tnoc_bfm_packet_type packet_type);
  return !is_response_packet(packet_type);
endfunction

function automatic bit is_posted_request_packet(tnoc_bfm_packet_type packet_type);
  return is_request_packet(packet_type) && (!packet_type[TNOC_BFM_NON_POSTED_BIT]);
endfunction

function automatic bit is_non_posted_packet(tnoc_bfm_packet_type packet_type);
  return is_request_packet(packet_type) && packet_type[TNOC_BFM_NON_POSTED_BIT];
endfunction

function automatic bit is_packet_with_payload(tnoc_bfm_packet_type packet_type);
  return packet_type[TNOC_BFM_PAYLOAD_BIT];
endfunction

function automatic bit is_packet_without_payload(tnoc_bfm_packet_type packet_type);
  return !is_packet_with_payload(packet_type);
endfunction

function automatic int calc_requst_burst_length(
  tnoc_bfm_address  address,
  int               byte_length,
  int               byte_width
);
  return (byte_length + (address % byte_width) + (byte_width - 1)) / byte_width;
endfunction

function automatic int calc_response_burst_length(
  int byte_offset,
  int byte_length,
  int byte_width
);
  return (byte_length + (byte_offset % byte_width) + (byte_width - 1)) / byte_width;
endfunction
`endif

