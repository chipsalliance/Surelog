interface rggen_wishbone_if
  import  rggen_rtl_pkg::*;
#(
  parameter int ADDRESS_WIDTH = 16,
  parameter int DATA_WIDTH    = 32
);
  logic                     cyc;
  logic                     stb;
  logic                     stall;
  logic [ADDRESS_WIDTH-1:0] adr;
  logic                     we;
  logic [DATA_WIDTH/8-1:0]  sel;
  logic                     ack;
  logic                     err;
  logic                     rty;
  logic [DATA_WIDTH-1:0]    dat_w;
  logic [DATA_WIDTH-1:0]    dat_r;

  modport master (
    output  cyc,
    output  stb,
    input   stall,
    output  adr,
    output  we,
    output  dat_w,
    output  sel,
    input   ack,
    input   err,
    input   rty,
    input   dat_r
  );

  modport slave (
    input   cyc,
    input   stb,
    output  stall,
    input   adr,
    input   we,
    input   dat_w,
    input   sel,
    output  ack,
    output  err,
    output  rty,
    output  dat_r
  );
endinterface
