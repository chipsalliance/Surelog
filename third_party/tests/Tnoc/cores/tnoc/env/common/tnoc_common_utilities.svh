`ifndef TNOC_COMMON_UTILITIES_SVH
`define TNOC_COMMON_UTILITIES_SVH
function automatic tnoc_bfm_location_id get_location_id(int y, int x);
  tnoc_bfm_location_id  id;
  id.y  = y;
  id.x  = x;
  return id;
endfunction
`endif
