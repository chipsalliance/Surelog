interface tnoc_axi_id_generator
  import  tnoc_pkg::*,
          tnoc_axi_pkg::*,
          tbcm_crc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter tnoc_axi_config     AXI_CONFIG    = TNOC_DEFAULT_AXI_CONFIG
)(
  tnoc_types      packet_types,
  tnoc_axi_types  axi_types
);
  localparam  int LOCATION_ID_WIDTH = get_location_id_width(PACKET_CONFIG);
  localparam  int TAG_WIDTH         = get_tag_width(PACKET_CONFIG);
  localparam  int KEY_WIDTH         = TAG_WIDTH + LOCATION_ID_WIDTH;
  localparam  int AXI_ID_WIDTH      = AXI_CONFIG.id_width;

  typedef packet_types.tnoc_location_id   tnoc_location_id;
  typedef packet_types.tnoc_tag           tnoc_tag;
  typedef packet_types.tnoc_header_fields tnoc_header_fields;
  typedef axi_types.tnoc_axi_id           tnoc_axi_id;

  if (KEY_WIDTH <= AXI_ID_WIDTH) begin : g
    function automatic tnoc_axi_id __get(
      tnoc_location_id  location_id,
      tnoc_tag          tag
    );
      return tnoc_axi_id'({tag, location_id});
    endfunction
  end
  else begin : g
    localparam  tbcm_crc_type CRC_TYPE  = TBCM_CRC_32C;
    localparam  int           CRC_WIDTH = get_crc_width(CRC_TYPE);

    tbcm_crc #(
      .DATA_WIDTH (KEY_WIDTH  ),
      .CRC_TYPE   (CRC_TYPE   )
    ) u_crc();

    function automatic tnoc_axi_id __get(
      tnoc_location_id  location_id,
      tnoc_tag          tag
    );
      logic [CRC_WIDTH-1:0] crc;
      crc = u_crc.get({tag, location_id});
      return crc[CRC_WIDTH-1-:AXI_ID_WIDTH];
    endfunction
  end

  function automatic tnoc_axi_id get(tnoc_header_fields header);
    return g.__get(header.source_id, header.tag);
  endfunction
endinterface
