interface rggen_bit_field_if #(
  parameter int WIDTH = 32
);
  logic             valid;
  logic [WIDTH-1:0] read_mask;
  logic [WIDTH-1:0] write_mask;
  logic [WIDTH-1:0] write_data;
  logic [WIDTH-1:0] read_data;
  logic [WIDTH-1:0] value;

  modport register (
    output  valid,
    output  read_mask,
    output  write_mask,
    output  write_data,
    input   read_data,
    input   value
  );

  modport bit_field (
    input   valid,
    input   read_mask,
    input   write_mask,
    input   write_data,
    output  read_data,
    output  value
  );

  modport monitor (
    input valid,
    input read_mask,
    input write_mask,
    input write_data,
    input read_data,
    input value
  );
endinterface
