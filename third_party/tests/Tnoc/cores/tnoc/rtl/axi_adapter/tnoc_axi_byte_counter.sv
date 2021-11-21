interface tnoc_axi_byte_counter
  import  tnoc_pkg::*,
          tnoc_axi_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter tnoc_axi_config     AXI_CONFIG    = TNOC_DEFAULT_AXI_CONFIG,
  parameter int                 COUNTER_WIDTH = get_default_counter_width(),
  parameter int                 OFFSET_WIDTH  = COUNTER_WIDTH
)(
  input var logic i_clk,
  input var logic i_rst_n
);
  localparam  int PACKET_BYTE_WIDTH       = PACKET_CONFIG.data_width / 8;
  localparam  int PACKET_BYTE_SIZE_WIDTH  = $clog2($clog2(PACKET_BYTE_WIDTH) + 1);
  localparam  int PACKET_COUNTER_WIDTH    = $clog2(PACKET_BYTE_WIDTH);
  localparam  int AXI_BYTE_WIDTH          = AXI_CONFIG.data_width / 8;
  localparam  int AXI_BYTE_SIZE_WIDTH     = $clog2($clog2(AXI_BYTE_WIDTH) + 1);
  localparam  int BYTE_SIZE_WIDTH         = AXI_BYTE_SIZE_WIDTH;
  localparam  int PACKET_MAX_BYTE_SIZE    = $clog2(PACKET_BYTE_WIDTH);

  logic                       initialize_valid;
  logic [BYTE_SIZE_WIDTH-1:0] initialize_byte_size;
  logic [COUNTER_WIDTH-1:0]   initialize_value;
  logic                       up_valid;
  logic [BYTE_SIZE_WIDTH-1:0] byte_size;
  logic [COUNTER_WIDTH-0:0]   byte_count;
  logic [COUNTER_WIDTH-0:0]   byte_count_next;
  logic [COUNTER_WIDTH-1:0]   byte_count_latched;

  function automatic void initialize(
    logic                       valid,
    logic [BYTE_SIZE_WIDTH-1:0] byte_size,
    logic [OFFSET_WIDTH-1:0]    offset
  );
    initialize_valid      = valid;
    initialize_byte_size  = byte_size;
    initialize_value      = COUNTER_WIDTH'(offset);
  endfunction

  function automatic void up(logic axi_ack, logic packet_ack);
    if (byte_size > PACKET_MAX_BYTE_SIZE) begin
      up_valid  = packet_ack;
    end
    else begin
      up_valid  = axi_ack;
    end
  endfunction

  function automatic logic is_axi_ready();
    return byte_count[byte_size] != byte_count_next[byte_size];
  endfunction

  function automatic logic is_packet_ready();
    return byte_count[PACKET_MAX_BYTE_SIZE] != byte_count_next[PACKET_MAX_BYTE_SIZE];
  endfunction

  function automatic logic is_active_byte(
    logic [PACKET_COUNTER_WIDTH-1:0]  index
  );
    logic [PACKET_COUNTER_WIDTH-0:0]  index_begin;
    logic [PACKET_COUNTER_WIDTH-0:0]  index_end;
    logic                             overflow;

    overflow    =
      byte_count[PACKET_COUNTER_WIDTH] != byte_count_next[PACKET_COUNTER_WIDTH];
    index_begin = {1'b0    , byte_count[PACKET_COUNTER_WIDTH-1:0]};
    index_end   = {overflow, byte_count_next[PACKET_COUNTER_WIDTH-1:0]};

    return
      ((PACKET_COUNTER_WIDTH + 1)'(index) >= index_begin) &&
      ((PACKET_COUNTER_WIDTH + 1)'(index) <  index_end  );
  endfunction

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      byte_size <= '0;
    end
    else if (initialize_valid) begin
      byte_size <= initialize_byte_size;
    end
  end

  always_comb begin
    byte_count      = {1'b0, byte_count_latched};
    byte_count_next =
      (COUNTER_WIDTH + 1)'(byte_count_latched & get_counter_mask(byte_size)) +
      get_increment_value(byte_size);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      byte_count_latched  <= '0;
    end
    else if (initialize_valid) begin
      byte_count_latched  <= initialize_value;
    end
    else if (up_valid) begin
      byte_count_latched  <= COUNTER_WIDTH'(byte_count_next);
    end
  end

  function automatic int get_default_counter_width();
    if (PACKET_CONFIG.data_width > AXI_CONFIG.data_width) begin
      return $clog2(PACKET_CONFIG.data_width) - 3;
    end
    else begin
      return $clog2(AXI_CONFIG.data_width) - 3;
    end
  endfunction

  function automatic logic [BYTE_SIZE_WIDTH-1:0] clip_byte_size(
    logic [BYTE_SIZE_WIDTH-1:0] byte_size
  );
    if (PACKET_BYTE_WIDTH >= AXI_BYTE_WIDTH) begin
      return byte_size;
    end
    else if (byte_size > PACKET_MAX_BYTE_SIZE) begin
      return PACKET_MAX_BYTE_SIZE;
    end
    else begin
      return byte_size;
    end
  endfunction

  function automatic logic [COUNTER_WIDTH-1:0] get_counter_mask(
    logic [BYTE_SIZE_WIDTH-1:0] byte_size
  );
    logic [COUNTER_WIDTH-1:0] mask;
    mask  = '1;
    mask  = mask << clip_byte_size(byte_size);
    return mask;
  endfunction

  function automatic logic [COUNTER_WIDTH-0:0] get_increment_value(
    logic [BYTE_SIZE_WIDTH-1:0] byte_size
  );
    logic [COUNTER_WIDTH-0:0] value;
    value                             = '0;
    value[clip_byte_size(byte_size)]  = '1;
    return value;
  endfunction
endinterface
