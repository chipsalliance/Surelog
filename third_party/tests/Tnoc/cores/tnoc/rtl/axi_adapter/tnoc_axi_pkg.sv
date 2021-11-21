`ifndef TNOC_AXI_PKG_SV
`define TNOC_AXI_PKG_SV

`ifndef TNOC_AXI_DEFAULT_ID_WIDTH
  `define TNOC_AXI_DEFAULT_ID_WIDTH  8
`endif

`ifndef TNOC_AXI_DEFAULT_ADDRESS_WIDTH
  `define TNOC_AXI_DEFAULT_ADDRESS_WIDTH  `TNOC_DEFAULT_ADDRESS_WIDTH
`endif

`ifndef TNOC_AXI_DEFAULT_DATA_WIDTH
  `define TNOC_AXI_DEFAULT_DATA_WIDTH `TNOC_DEFAULT_DATA_WIDTH
`endif

`ifndef TNOC_AXI_DEFAULT_QOS_WIDTH
  `define TNOC_AXI_DEFAULT_QOS_WIDTH  0
`endif

package tnoc_axi_pkg;
  typedef struct packed {
    shortint  id_width;
    shortint  address_width;
    shortint  data_width;
    shortint  qos_width;
  } tnoc_axi_config;

  localparam  tnoc_axi_config TNOC_DEFAULT_AXI_CONFIG = '{
    id_width:       `TNOC_AXI_DEFAULT_ID_WIDTH,
    address_width:  `TNOC_AXI_DEFAULT_ADDRESS_WIDTH,
    data_width:     `TNOC_AXI_DEFAULT_DATA_WIDTH,
    qos_width:      `TNOC_AXI_DEFAULT_QOS_WIDTH
  };

  typedef logic [7:0] tnoc_axi_burst_length;
  typedef logic [8:0] tnoc_axi_unpacked_burst_length;

  function automatic tnoc_axi_burst_length pack_burst_length(
    tnoc_axi_unpacked_burst_length  burst_length
  );
    return tnoc_axi_burst_length'(burst_length - 1);
  endfunction

  function automatic tnoc_axi_unpacked_burst_length unpack_burst_length(
    tnoc_axi_burst_length burst_length
  );
    return tnoc_axi_unpacked_burst_length'(burst_length) + 1;
  endfunction

  typedef enum logic [2:0] {
    TNOC_AXI_BURST_SIZE_1_BYTE    = 0,
    TNOC_AXI_BURST_SIZE_2_BYTES   = 1,
    TNOC_AXI_BURST_SIZE_4_BYTES   = 2,
    TNOC_AXI_BURST_SIZE_8_BYTES   = 3,
    TNOC_AXI_BURST_SIZE_16_BYTES  = 4,
    TNOC_AXI_BURST_SIZE_32_BYTES  = 5,
    TNOC_AXI_BURST_SIZE_64_BYTES  = 6,
    TNOC_AXI_BURST_SIZE_128_BYTES = 7
  } tnoc_axi_burst_size;

  typedef enum logic [1:0] {
    TNOC_AXI_FIXED_BURST        = 0,
    TNOC_AXI_INCREMENTING_BURST = 1,
    TNOC_AXI_WRAP_BURST         = 2
  } tnoc_axi_burst_type;

  typedef enum logic [1:0] {
    TNOC_AXI_OKAY         = 0,
    TNOC_AXI_EXOKAY       = 1,
    TNOC_AXI_SLAVE_ERROR  = 2,
    TNOC_AXI_DECODE_ERROR = 3
  } tnoc_axi_response;

  function automatic tnoc_axi_response convert_to_axi_status(
    tnoc_pkg::tnoc_response_status  status
  );
    case (1'b1)
      status.decode_error:  return TNOC_AXI_DECODE_ERROR;
      status.slave_error:   return TNOC_AXI_SLAVE_ERROR;
      status.exokay:        return TNOC_AXI_EXOKAY;
      default:              return TNOC_AXI_OKAY;
    endcase
  endfunction

  function automatic tnoc_pkg::tnoc_response_status convert_from_axi_status(
    tnoc_axi_response status
  );
    case (status)
      TNOC_AXI_OKAY:          return '{                     default: 1'b0 };
      TNOC_AXI_EXOKAY:        return '{ exokay:       1'b1, default: 1'b0 };
      TNOC_AXI_SLAVE_ERROR:   return '{ slave_error:  1'b1, default: 1'b0 };
      TNOC_AXI_DECODE_ERROR:  return '{ decode_error: 1'b1, default: 1'b0 };
    endcase
  endfunction

  typedef logic [3:0] tnoc_axi_qos;
endpackage
`endif
