module tnoc_flit_array_if_connector
  import  tnoc_config_pkg::*;
#(
  parameter   tnoc_config CONFIG      = TNOC_DEFAULT_CONFIG,
  parameter   int         IFS         = 1,
  parameter   bit         ACTIVE_MODE = 1,
  localparam  int         CHANNELS    = CONFIG.virtual_channels
)(
  tnoc_flit_if      flit_in_if[IFS],
  tnoc_flit_if      flit_out_if[IFS],
  tnoc_bfm_flit_if  flit_bfm_in_if[CHANNELS*IFS],
  tnoc_bfm_flit_if  flit_bfm_out_if[CHANNELS*IFS]
);
  `include  "tnoc_macros.svh"
  for (genvar i = 0;i < IFS;++i) begin
    tnoc_flit_if_connector #(
      CONFIG, ACTIVE_MODE
    ) u_connector (
      flit_in_if[i],
      flit_out_if[i],
      `tnoc_array_slicer(flit_bfm_in_if , i, CHANNELS),
      `tnoc_array_slicer(flit_bfm_out_if, i, CHANNELS)
    );
  end
endmodule
