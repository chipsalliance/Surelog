interface rggen_axi4lite_if
  import  rggen_rtl_pkg::*;
#(
  parameter int ID_WIDTH      = 0,
  parameter int ADDRESS_WIDTH = 16,
  parameter int BUS_WIDTH     = 32
);
  localparam  int ACTUAL_ID_WIDTH = rggen_clip_width(ID_WIDTH);

  logic                       awvalid;
  logic                       awready;
  logic [ACTUAL_ID_WIDTH-1:0] awid;
  logic [ADDRESS_WIDTH-1:0]   awaddr;
  logic [2:0]                 awprot;
  logic                       wvalid;
  logic                       wready;
  logic [BUS_WIDTH-1:0]       wdata;
  logic [BUS_WIDTH/8-1:0]     wstrb;
  logic                       bvalid;
  logic                       bready;
  logic [ACTUAL_ID_WIDTH-1:0] bid;
  logic [1:0]                 bresp;
  logic                       arvalid;
  logic                       arready;
  logic [ADDRESS_WIDTH-1:0]   araddr;
  logic [ACTUAL_ID_WIDTH-1:0] arid;
  logic [2:0]                 arprot;
  logic                       rvalid;
  logic                       rready;
  logic [ACTUAL_ID_WIDTH-1:0] rid;
  logic [1:0]                 rresp;
  logic [BUS_WIDTH-1:0]       rdata;

  modport master (
    output  awvalid,
    input   awready,
    output  awid,
    output  awaddr,
    output  awprot,
    output  wvalid,
    input   wready,
    output  wdata,
    output  wstrb,
    input   bvalid,
    output  bready,
    input   bid,
    input   bresp,
    output  arvalid,
    input   arready,
    output  arid,
    output  araddr,
    output  arprot,
    input   rvalid,
    output  rready,
    input   rid,
    input   rresp,
    input   rdata
  );

  modport slave (
    input   awvalid,
    output  awready,
    input   awid,
    input   awaddr,
    input   awprot,
    input   wvalid,
    output  wready,
    input   wdata,
    input   wstrb,
    output  bvalid,
    input   bready,
    output  bid,
    output  bresp,
    input   arvalid,
    output  arready,
    input   arid,
    input   araddr,
    input   arprot,
    output  rvalid,
    input   rready,
    output  rid,
    output  rresp,
    output  rdata
  );

  modport monitor (
    input awvalid,
    input awready,
    input awid,
    input awaddr,
    input awprot,
    input wvalid,
    input wready,
    input wdata,
    input wstrb,
    input bvalid,
    input bready,
    input bid,
    input bresp,
    input arvalid,
    input arready,
    input arid,
    input araddr,
    input arprot,
    input rvalid,
    input rready,
    input rid,
    input rresp,
    input rdata
  );
endinterface
