`ifndef TNOC_BFM_TYPES_PKG_SV
`define TNOC_BFM_TYPES_PKG_SV

`ifndef TNOC_BFM_MAX_ID_X_WIDTH
  `define TNOC_BFM_MAX_ID_X_WIDTH 8
`endif

`ifndef TNOC_BFM_MAX_ID_Y_WIDTH
  `define TNOC_BFM_MAX_ID_Y_WIDTH 8
`endif

`ifndef TNOC_BFM_MAX_VIRTUAL_CHANNELS
  `define TNOC_BFM_MAX_VIRTUAL_CHANNELS 4
`endif

`ifndef TNOC_BFM_MAX_TAGS
  `define TNOC_BFM_MAX_TAGS 256
`endif

`ifndef TNOC_BFM_MAX_ADDRESS_WIDTH
  `define TNOC_BFM_MAX_ADDRESS_WIDTH  64
`endif

`ifndef TNOC_BFM_MAX_DATA_WIDTH
  `define TNOC_BFM_MAX_DATA_WIDTH 256
`endif

`ifndef TNOC_BFM_MAX_BYTE_LENGTH
  `define TNOC_BFM_MAX_BYTE_LENGTH  4096
`endif

package tnoc_bfm_types_pkg;
  `define tnoc_bfm_calc_width(VALUE) (((VALUE) <= 1) ? 1 : $clog2((VALUE)))

  typedef enum bit [7:0] {
    TNOC_BFM_READ               = 'b001_00000,
    TNOC_BFM_POSTED_WRITE       = 'b010_00000,
    TNOC_BFM_NON_POSTED_WRITE   = 'b011_00000,
    TNOC_BFM_RESPONSE           = 'b100_00000,
    TNOC_BFM_RESPONSE_WITH_DATA = 'b110_00000
  } tnoc_bfm_packet_type;

  localparam  int TNOC_BFM_RESPONSE_BIT   = 7;
  localparam  int TNOC_BFM_PAYLOAD_BIT    = 6;
  localparam  int TNOC_BFM_NON_POSTED_BIT = 5;

  typedef bit [`TNOC_BFM_MAX_ID_X_WIDTH-1:0]  tnoc_bfm_id_x;
  typedef bit [`TNOC_BFM_MAX_ID_Y_WIDTH-1:0]  tnoc_bfm_id_y;
  typedef struct packed {
    tnoc_bfm_id_x  x;
    tnoc_bfm_id_y  y;
  } tnoc_bfm_location_id;

  localparam  int TNOC_BFM_VC_WIDTH = `tnoc_bfm_calc_width(`TNOC_BFM_MAX_VIRTUAL_CHANNELS);
  typedef bit [TNOC_BFM_VC_WIDTH-1:0] tnoc_bfm_vc;

  localparam  int TNOC_BFM_TAG_WIDTH  = `tnoc_bfm_calc_width(`TNOC_BFM_MAX_TAGS);
  typedef bit [TNOC_BFM_TAG_WIDTH-1:0]  tnoc_bfm_tag;

  typedef enum bit [1:0] {
    TNOC_BFM_FIXED_BURST        = 'b00,
    TNOC_BFM_INCREMENTING_BURST = 'b01,
    TNOC_BFM_WRAPPING_BURST     = 'b10
  } tnoc_bfm_burst_type;

  localparam  int TNOC_BFM_BYTE_LENGTH_WIDTH  = `tnoc_bfm_calc_width(`TNOC_BFM_MAX_BYTE_LENGTH);
  typedef bit [TNOC_BFM_BYTE_LENGTH_WIDTH-1:0]  tnoc_bfm_byte_length;

  localparam  int TNOC_BFM_BYTE_SIZE_WIDTH  = `tnoc_bfm_calc_width($clog2(`TNOC_BFM_MAX_DATA_WIDTH / 8) + 1);
  typedef bit [TNOC_BFM_BYTE_SIZE_WIDTH-1:0]  tnoc_bfm_byte_size;

  typedef bit [`TNOC_BFM_MAX_ADDRESS_WIDTH-1:0] tnoc_bfm_address;

  localparam  int TNOC_BFM_BYTE_OFFSET_WIDTH  = `tnoc_bfm_calc_width(`TNOC_BFM_MAX_DATA_WIDTH / 8);
  typedef bit [TNOC_BFM_BYTE_OFFSET_WIDTH-1:0]  tnoc_bfm_byte_offset;

  localparam  int TNOC_BFM_BYTE_END_WIDTH = `tnoc_bfm_calc_width(`TNOC_BFM_MAX_DATA_WIDTH / 8);
  typedef bit [TNOC_BFM_BYTE_END_WIDTH-1:0] tnoc_bfm_byte_end;

  typedef struct packed {
    bit exokay;
    bit slave_error;
    bit decode_error;
  } tnoc_bfm_response_status;

  localparam  int TNOC_BFM_COMMON_HEADER_WIDTH  =
    $bits(tnoc_bfm_packet_type ) +
    $bits(tnoc_bfm_location_id ) +
    $bits(tnoc_bfm_location_id ) +
    $bits(tnoc_bfm_vc          ) +
    $bits(tnoc_bfm_tag         ) +
    1;                              //  invalid destination flag
  localparam  int TNOC_BFM_REQUEST_HEADER_WIDTH =
    TNOC_BFM_COMMON_HEADER_WIDTH +
    $bits(tnoc_bfm_byte_size  )  +
    $bits(tnoc_bfm_byte_length)  +
    $bits(tnoc_bfm_address    )  +
    $bits(tnoc_bfm_burst_type );
  localparam  int TNOC_BFM_RESPONSE_HEADER_WIDTH  =
    TNOC_BFM_COMMON_HEADER_WIDTH    +
    $bits(tnoc_bfm_byte_size      ) +
    $bits(tnoc_bfm_byte_offset    ) +
    $bits(tnoc_bfm_response_status);
  localparam  int TNOC_BFM_HEADER_WIDTH  = (
    TNOC_BFM_REQUEST_HEADER_WIDTH > TNOC_BFM_RESPONSE_HEADER_WIDTH
  ) ? TNOC_BFM_REQUEST_HEADER_WIDTH : TNOC_BFM_RESPONSE_HEADER_WIDTH;

  typedef bit [`TNOC_BFM_MAX_DATA_WIDTH-1:0]    tnoc_bfm_data;
  typedef bit [`TNOC_BFM_MAX_DATA_WIDTH/8-1:0]  tnoc_bfm_byte_enable;

  localparam  int TNOC_BFM_REQUEST_PAYLOAD_WIDTH  =
    $bits(tnoc_bfm_data       ) + //  data
    $bits(tnoc_bfm_byte_enable);  //  byte enable

  localparam  int TNOC_BFM_RESPONSE_PAYLOAD_WIDTH =
    $bits(tnoc_bfm_data           ) + //  data
    $bits(tnoc_bfm_response_status) + //  error status
    $bits(tnoc_bfm_byte_end       ) + //  byte end
    1;                                //  last

  localparam  int TNOC_BFM_PAYLOAD_WIDTH  = (
    TNOC_BFM_REQUEST_PAYLOAD_WIDTH > TNOC_BFM_RESPONSE_PAYLOAD_WIDTH
  ) ? TNOC_BFM_REQUEST_PAYLOAD_WIDTH : TNOC_BFM_RESPONSE_PAYLOAD_WIDTH;

  typedef enum bit {
    TNOC_BFM_HEADER_FLIT,
    TNOC_BFM_PAYLOAD_FLIT
  } tnoc_bfm_flit_type;

  localparam  int TNOC_FLIT_DATA_WIDTH = (
    TNOC_BFM_COMMON_HEADER_WIDTH > TNOC_BFM_PAYLOAD_WIDTH
  ) ? TNOC_BFM_COMMON_HEADER_WIDTH : TNOC_BFM_PAYLOAD_WIDTH;

  typedef bit [TNOC_FLIT_DATA_WIDTH-1:0]  tnoc_bfm_flit_data;

  typedef struct packed {
    tnoc_bfm_flit_type  flit_type;
    bit                 head;
    bit                 tail;
    tnoc_bfm_flit_data  data;
  } tnoc_bfm_flit;

  `undef  tnoc_bfm_calc_width
endpackage
`endif
