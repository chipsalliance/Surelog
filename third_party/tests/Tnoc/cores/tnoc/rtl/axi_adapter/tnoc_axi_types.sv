`ifndef TNOC_AXI_TYPES_SV
`define TNOC_AXI_TYPES_SV
interface tnoc_axi_types
  import  tnoc_axi_pkg::*;
#(
  tnoc_axi_config AXI_CONFIG  = TNOC_DEFAULT_AXI_CONFIG
);
  typedef logic [AXI_CONFIG.id_width-1:0]       tnoc_axi_id;
  typedef logic [AXI_CONFIG.address_width-1:0]  tnoc_axi_address;
  typedef logic [AXI_CONFIG.data_width-1:0]     tnoc_axi_data;
  typedef logic [AXI_CONFIG.data_width/8-1:0]   tnoc_axi_strobe;
endinterface
`endif
