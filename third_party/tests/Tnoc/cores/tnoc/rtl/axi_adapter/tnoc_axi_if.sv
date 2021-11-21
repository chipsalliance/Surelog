`ifndef TNOC_AXI_IF_SV
`define TNOC_AXI_IF_SV
interface tnoc_axi_if
  import  tnoc_axi_pkg::*;
#(
  parameter tnoc_axi_config AXI_CONFIG  = '0
)(
  tnoc_axi_types  axi_types
);
  typedef axi_types.tnoc_axi_id       tnoc_axi_id;
  typedef axi_types.tnoc_axi_address  tnoc_axi_address;
  typedef axi_types.tnoc_axi_data     tnoc_axi_data;
  typedef axi_types.tnoc_axi_strobe   tnoc_axi_strobe;

  //  Write Address Channel
  logic                 awvalid;
  logic                 awready;
  tnoc_axi_id           awid;
  tnoc_axi_address      awaddr;
  tnoc_axi_burst_length awlen;
  tnoc_axi_burst_size   awsize;
  tnoc_axi_burst_type   awburst;
  tnoc_axi_qos          awqos;
  //  Write Data Channel
  logic                 wvalid;
  logic                 wready;
  tnoc_axi_data         wdata;
  tnoc_axi_strobe       wstrb;
  logic                 wlast;
  //  Write Response Channel
  logic                 bvalid;
  logic                 bready;
  tnoc_axi_id           bid;
  tnoc_axi_response     bresp;
  //  Read Address Channel
  logic                 arvalid;
  logic                 arready;
  tnoc_axi_id           arid;
  tnoc_axi_address      araddr;
  tnoc_axi_burst_length arlen;
  tnoc_axi_burst_size   arsize;
  tnoc_axi_burst_type   arburst;
  tnoc_axi_qos          arqos;
  //  Read Response Channel
  logic                 rvalid;
  logic                 rready;
  tnoc_axi_id           rid;
  tnoc_axi_data         rdata;
  tnoc_axi_response     rresp;
  logic                 rlast;

  function automatic logic get_awchannel_ack();
    return awvalid & awready;
  endfunction

  function automatic logic get_wchannel_ack();
    return wvalid & wready;
  endfunction

  function automatic logic get_bchannel_ack();
    return bvalid & bready;
  endfunction

  function automatic logic get_archannel_ack();
    return arvalid & arready;
  endfunction

  function automatic logic get_rchannel_ack();
    return rvalid & rready;
  endfunction

  modport master (
    output  awvalid,
    input   awready,
    output  awid,
    output  awaddr,
    output  awlen,
    output  awsize,
    output  awburst,
    output  awqos,
    output  wvalid,
    input   wready,
    output  wdata,
    output  wstrb,
    output  wlast,
    input   bvalid,
    output  bready,
    input   bid,
    input   bresp,
    output  arvalid,
    input   arready,
    output  arid,
    output  araddr,
    output  arlen,
    output  arsize,
    output  arburst,
    output  arqos,
    input   rvalid,
    output  rready,
    input   rid,
    input   rdata,
    input   rresp,
    input   rlast,
    import  get_awchannel_ack,
    import  get_wchannel_ack,
    import  get_bchannel_ack,
    import  get_archannel_ack,
    import  get_rchannel_ack
  );

  modport master_write (
    output  awvalid,
    input   awready,
    output  awid,
    output  awaddr,
    output  awlen,
    output  awsize,
    output  awburst,
    output  awqos,
    output  wvalid,
    input   wready,
    output  wdata,
    output  wstrb,
    output  wlast,
    input   bvalid,
    output  bready,
    input   bid,
    input   bresp,
    import  get_awchannel_ack,
    import  get_wchannel_ack,
    import  get_bchannel_ack
  );

  modport master_read (
    output  arvalid,
    input   arready,
    output  arid,
    output  araddr,
    output  arlen,
    output  arsize,
    output  arburst,
    output  arqos,
    input   rvalid,
    output  rready,
    input   rid,
    input   rdata,
    input   rresp,
    input   rlast,
    import  get_archannel_ack,
    import  get_rchannel_ack
  );

  modport slave (
    input   awvalid,
    output  awready,
    input   awid,
    input   awaddr,
    input   awlen,
    input   awsize,
    input   awburst,
    input   awqos,
    input   wvalid,
    output  wready,
    input   wdata,
    input   wstrb,
    input   wlast,
    output  bvalid,
    input   bready,
    output  bid,
    output  bresp,
    input   arvalid,
    output  arready,
    input   arid,
    input   araddr,
    input   arlen,
    input   arsize,
    input   arburst,
    input   arqos,
    output  rvalid,
    input   rready,
    output  rid,
    output  rdata,
    output  rresp,
    output  rlast,
    import  get_awchannel_ack,
    import  get_wchannel_ack,
    import  get_bchannel_ack,
    import  get_archannel_ack,
    import  get_rchannel_ack
  );

  modport slave_write (
    input   awvalid,
    output  awready,
    input   awid,
    input   awaddr,
    input   awlen,
    input   awsize,
    input   awburst,
    input   awqos,
    input   wvalid,
    output  wready,
    input   wdata,
    input   wstrb,
    input   wlast,
    output  bvalid,
    input   bready,
    output  bid,
    output  bresp,
    import  get_awchannel_ack,
    import  get_wchannel_ack,
    import  get_bchannel_ack
  );

  modport slave_read (
    input   arvalid,
    output  arready,
    input   arid,
    input   araddr,
    input   arlen,
    input   arsize,
    input   arburst,
    input   arqos,
    output  rvalid,
    input   rready,
    output  rid,
    output  rdata,
    output  rresp,
    output  rlast,
    import  get_archannel_ack,
    import  get_rchannel_ack
  );
endinterface
`endif
