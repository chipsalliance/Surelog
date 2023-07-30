interface rggen_bus_if #(
  parameter int ADDRESS_WIDTH = 16,
  parameter int BUS_WIDTH     = 32
);
  import  rggen_rtl_pkg::*;

  logic                     valid;
  rggen_access              access;
  logic [ADDRESS_WIDTH-1:0] address;
  logic [BUS_WIDTH-1:0]     write_data;
  logic [BUS_WIDTH/8-1:0]   strobe;
  logic                     ready;
  rggen_status              status;
  logic [BUS_WIDTH-1:0]     read_data;

  modport master (
    output  valid,
    output  access,
    output  address,
    output  write_data,
    output  strobe,
    input   ready,
    input   status,
    input   read_data
  );

  modport slave (
    input   valid,
    input   access,
    input   address,
    input   write_data,
    input   strobe,
    output  ready,
    output  status,
    output  read_data
  );

  modport monitor (
    input valid,
    input access,
    input address,
    input write_data,
    input strobe,
    input ready,
    input status,
    input read_data
  );
endinterface
