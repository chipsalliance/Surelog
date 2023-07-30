interface rggen_apb_if #(
  parameter int ADDRESS_WIDTH = 16,
  parameter int BUS_WIDTH     = 32
);
  logic                     psel;
  logic                     penable;
  logic [ADDRESS_WIDTH-1:0] paddr;
  logic [2:0]               pprot;
  logic                     pwrite;
  logic [BUS_WIDTH/8-1:0]   pstrb;
  logic [BUS_WIDTH-1:0]     pwdata;
  logic                     pready;
  logic [BUS_WIDTH-1:0]     prdata;
  logic                     pslverr;

  modport master (
    output  psel,
    output  penable,
    output  paddr,
    output  pprot,
    output  pwrite,
    output  pstrb,
    output  pwdata,
    input   pready,
    input   prdata,
    input   pslverr
  );

  modport slave (
    input   psel,
    input   penable,
    input   paddr,
    input   pprot,
    input   pwrite,
    input   pstrb,
    input   pwdata,
    output  pready,
    output  prdata,
    output  pslverr
  );

  modport monitor (
    input psel,
    input penable,
    input paddr,
    input pprot,
    input pwrite,
    input pstrb,
    input pwdata,
    input pready,
    input prdata,
    input pslverr
  );
endinterface
