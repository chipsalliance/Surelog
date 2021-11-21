module tnoc_axi_if_connector (
  tnoc_axi_if.slave   slave_if,
  tnoc_axi_if.master  master_if
);
  always_comb begin
    master_if.awvalid = slave_if.awvalid;
    slave_if.awready  = master_if.awready;
    master_if.awid    = slave_if.awid;
    master_if.awaddr  = slave_if.awaddr;
    master_if.awlen   = slave_if.awlen;
    master_if.awsize  = slave_if.awsize;
    master_if.awburst = slave_if.awburst;
    master_if.awqos   = slave_if.awqos;
    master_if.wvalid  = slave_if.wvalid;
    slave_if.wready   = master_if.wready;
    master_if.wdata   = slave_if.wdata;
    master_if.wstrb   = slave_if.wstrb;
    master_if.wlast   = slave_if.wlast;
    slave_if.bvalid   = master_if.bvalid;
    master_if.bready  = slave_if.bready;
    slave_if.bid      = master_if.bid;
    slave_if.bresp    = master_if.bresp;
  end

  always_comb begin
    master_if.arvalid = slave_if.arvalid;
    slave_if.arready  = master_if.arready;
    master_if.arid    = slave_if.arid;
    master_if.araddr  = slave_if.araddr;
    master_if.arlen   = slave_if.arlen;
    master_if.arsize  = slave_if.arsize;
    master_if.arburst = slave_if.arburst;
    master_if.arqos   = slave_if.arqos;
    slave_if.rvalid   = master_if.rvalid;
    master_if.rready  = slave_if.rready;
    slave_if.rid      = master_if.rid;
    slave_if.rdata    = master_if.rdata;
    slave_if.rresp    = master_if.rresp;
    slave_if.rlast    = master_if.rlast;
  end
endmodule
