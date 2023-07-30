module rggen_address_decoder
  import  rggen_rtl_pkg::*;
#(
  parameter bit             READABLE      = 1,
  parameter bit             WRITABLE      = 1,
  parameter int             WIDTH         = 8,
  parameter int             BUS_WIDTH     = 32,
  parameter bit [WIDTH-1:0] START_ADDRESS = '0,
  parameter int             BYTE_SIZE     = 0
)(
  input   logic [WIDTH-1:0] i_address,
  input   rggen_access      i_access,
  input   logic             i_additional_match,
  output  logic             o_match
);
  localparam  int                 LSB           = $clog2(BUS_WIDTH) - 3;
  localparam  bit [WIDTH-LSB-1:0] BEGIN_ADDRESS = START_ADDRESS[WIDTH-1:LSB];
  localparam  bit [WIDTH-LSB-1:0] END_ADDRESS   = calc_end_address(START_ADDRESS, BYTE_SIZE);

  function automatic bit [WIDTH-LSB-1:0] calc_end_address(
    bit [WIDTH-1:0] start_address,
    int             byte_size
  );
    bit [WIDTH-1:0] end_address;
    end_address = start_address + WIDTH'(byte_size - 1);
    return end_address[WIDTH-1:LSB];
  endfunction

  logic address_match;
  logic access_match;

  generate
    if (BEGIN_ADDRESS == END_ADDRESS) begin : g_address_matcher
      assign  address_match = i_address[WIDTH-1:LSB] == BEGIN_ADDRESS;
    end
    else if ((BEGIN_ADDRESS != '0) && (END_ADDRESS != '1)) begin : g_address_matcher
      assign  address_match =
        (i_address[WIDTH-1:LSB] >= BEGIN_ADDRESS) &&
        (i_address[WIDTH-1:LSB] <= END_ADDRESS  );
    end
    else if ((BEGIN_ADDRESS == '0) && (END_ADDRESS != '1)) begin : g_address_matcher
      assign  address_match = i_address[WIDTH-1:LSB] <= END_ADDRESS;
    end
    else if ((BEGIN_ADDRESS != '0) && (END_ADDRESS == '1)) begin : g_address_matcher
      assign  address_match = i_address[WIDTH-1:LSB] >= BEGIN_ADDRESS;
    end
    else begin : g_address_matcher
      assign  address_match = '1;
    end

    if (READABLE && WRITABLE) begin : g_access_matcher
      assign  access_match  = '1;
    end
    else if (READABLE) begin : g_access_matcher
      assign  access_match  = (!i_access[RGGEN_ACCESS_DATA_BIT]);
    end
    else begin : g_access_matcher
      assign  access_match  = i_access[RGGEN_ACCESS_DATA_BIT];
    end
  endgenerate

  assign  o_match = address_match && access_match && i_additional_match;
endmodule
