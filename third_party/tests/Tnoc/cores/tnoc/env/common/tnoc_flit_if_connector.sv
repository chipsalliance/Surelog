module tnoc_flit_if_connector
  `include  "tnoc_default_imports.svh"
#(
  parameter   tnoc_config CONFIG      = TNOC_DEFAULT_CONFIG,
  parameter   bit         ACTIVE_MODE = 1,
  localparam  int         CHANNELS    = CONFIG.virtual_channels
)(
  tnoc_flit_if      flit_in_if,
  tnoc_flit_if      flit_out_if,
  tnoc_bfm_flit_if  flit_bfm_in_if[CHANNELS],
  tnoc_bfm_flit_if  flit_bfm_out_if[CHANNELS]
);
  import  tnoc_bfm_types_pkg::*;

  `include  "tnoc_packet_flit_macros.svh"
  `tnoc_define_packet_and_flit(CONFIG)

  function automatic tnoc_flit convert_to_dut_flit(tnoc_bfm_flit bfm_flit);
    tnoc_flit dut_flit;
    dut_flit.flit_type  = tnoc_flit_type'(bfm_flit.flit_type);
    dut_flit.head       = bfm_flit.head;
    dut_flit.tail       = bfm_flit.tail;
    dut_flit.data       = bfm_flit.data;
    return dut_flit;
  endfunction

  function automatic tnoc_bfm_flit convert_to_bfm_flit(tnoc_flit dut_flit);
    tnoc_bfm_flit bfm_flit;
    bfm_flit.flit_type  = tnoc_bfm_flit_type'(dut_flit.flit_type);
    bfm_flit.head       = dut_flit.head;
    bfm_flit.tail       = dut_flit.tail;
    bfm_flit.data       = dut_flit.data;
    return bfm_flit;
  endfunction

  for (genvar i = 0;i < CHANNELS;++i) begin
    if (ACTIVE_MODE) begin
      assign  flit_in_if.valid[i]             = flit_bfm_in_if[i].valid;
      assign  flit_bfm_in_if[i].ready         = flit_in_if.ready[i];
      assign  flit_in_if.flit[i]              = convert_to_dut_flit(flit_bfm_in_if[i].flit);
      assign  flit_bfm_in_if[i].vc_available  = flit_in_if.vc_available[i];

      assign  flit_bfm_out_if[i].valid    = flit_out_if.valid[i];
      assign  flit_out_if.ready[i]        = flit_bfm_out_if[i].ready;
      assign  flit_bfm_out_if[i].flit     = convert_to_bfm_flit(flit_out_if.flit[i]);
      assign  flit_out_if.vc_available[i] = flit_bfm_out_if[i].vc_available;
    end
    else begin
      assign  flit_bfm_in_if[i].valid         = flit_in_if.valid[i];
      assign  flit_bfm_in_if[i].ready         = flit_in_if.ready[i];
      assign  flit_bfm_in_if[i].flit          = convert_to_bfm_flit(flit_in_if.flit[i]);
      assign  flit_bfm_in_if[i].vc_available  = flit_in_if.vc_available[i];

      assign  flit_bfm_out_if[i].valid        = flit_out_if.valid[i];
      assign  flit_bfm_out_if[i].ready        = flit_out_if.ready[i];
      assign  flit_bfm_out_if[i].flit         = convert_to_bfm_flit(flit_out_if.flit[i]);
      assign  flit_bfm_out_if[i].vc_available = flit_out_if.vc_available[i];
    end
  end
endmodule
