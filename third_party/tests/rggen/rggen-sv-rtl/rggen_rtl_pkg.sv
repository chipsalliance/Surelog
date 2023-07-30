package rggen_rtl_pkg;
  typedef enum logic [1:0] {
    RGGEN_READ          = 2'b10,
    RGGEN_POSTED_WRITE  = 2'b01,
    RGGEN_WRITE         = 2'b11
  } rggen_access;

  localparam  int RGGEN_ACCESS_DATA_BIT       = 0;
  localparam  int RGGEN_ACCESS_NON_POSTED_BIT = 1;

  typedef enum logic [1:0] {
    RGGEN_OKAY          = 2'b00,
    RGGEN_EXOKAY        = 2'b01,
    RGGEN_SLAVE_ERROR   = 2'b10,
    RGGEN_DECODE_ERROR  = 2'b11
  } rggen_status;

  typedef enum logic {
    RGGEN_SW_ACCESS,
    RGGEN_HW_ACCESS
  } rggen_sw_hw_access;

  typedef enum logic {
    RGGEN_ACTIVE_LOW  = 1'b0,
    RGGEN_ACTIVE_HIGH = 1'b1
  } rggen_polarity;

  typedef enum logic [3:0] {
    RGGEN_READ_NONE,
    RGGEN_READ_DEFAULT,
    RGGEN_READ_CLEAR,
    RGGEN_READ_SET,
    RGGEN_WRITE_NONE,
    RGGEN_WRITE_DEFAULT,
    RGGEN_WRITE_0_CLEAR,
    RGGEN_WRITE_1_CLEAR,
    RGGEN_WRITE_CLEAR,
    RGGEN_WRITE_0_SET,
    RGGEN_WRITE_1_SET,
    RGGEN_WRITE_SET,
    RGGEN_WRITE_0_TOGGLE,
    RGGEN_WRITE_1_TOGGLE
  } rggen_sw_action;

  function automatic int rggen_clip_width(int width);
    return (width > 0) ? width : 1;
  endfunction
endpackage
