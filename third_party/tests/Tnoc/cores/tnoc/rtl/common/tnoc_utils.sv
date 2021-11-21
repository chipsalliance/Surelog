interface tnoc_utils
  import  tnoc_pkg::*;
#(
  tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG
)(
  tnoc_types  types
);
  typedef types.tnoc_byte_length  tnoc_byte_length;
  typedef types.tnoc_address      tnoc_address;
  typedef types.tnoc_burst_length tnoc_burst_length;

  localparam  int BYTE_WIDTH  = PACKET_CONFIG.data_width / 8;
  localparam  int SHIFT_SIZE  = $clog2(BYTE_WIDTH);

  function automatic tnoc_burst_length calc_burst_length(
    tnoc_byte_length  byte_length,
    tnoc_address      address
  );
    tnoc_byte_length  offset;
    tnoc_burst_length burst_length;
    offset        = tnoc_byte_length'(address[SHIFT_SIZE-1:0]);
    burst_length  = tnoc_burst_length'(
      (byte_length + offset + tnoc_burst_length'(BYTE_WIDTH - 1)) >> SHIFT_SIZE
    );
    return burst_length;
  endfunction
endinterface
