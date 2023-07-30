module rggen_axi4lite_skid_buffer
  import  rggen_rtl_pkg::*;
#(
  parameter int ID_WIDTH      = 0,
  parameter int ADDRESS_WIDTH = 8,
  parameter int BUS_WIDTH     = 32
)(
  input logic               i_clk,
  input logic               i_rst_n,
  rggen_axi4lite_if.slave   slave_if,
  rggen_axi4lite_if.master  master_if
);
  logic                                   awvalid;
  logic [rggen_clip_width(ID_WIDTH)-1:0]  awid;
  logic [ADDRESS_WIDTH-1:0]               awaddr;
  logic [2:0]                             awprot;
  logic                                   wvalid;
  logic [BUS_WIDTH-1:0]                   wdata;
  logic [BUS_WIDTH/8-1:0]                 wstrb;
  logic                                   arvalid;
  logic                                   arready;
  logic [ADDRESS_WIDTH-1:0]               araddr;
  logic [rggen_clip_width(ID_WIDTH)-1:0]  arid;
  logic [2:0]                             arprot;

  //  Write address channel
  always_comb begin
    slave_if.awready  = !awvalid;
  end

  always_comb begin
    master_if.awvalid = slave_if.awvalid || awvalid;
  end

  always_comb begin
    if (awvalid) begin
      master_if.awid    = awid;
      master_if.awaddr  = awaddr;
      master_if.awprot  = awprot;
    end
    else begin
      master_if.awid    = slave_if.awid;
      master_if.awaddr  = ADDRESS_WIDTH'(slave_if.awaddr);
      master_if.awprot  = slave_if.awprot;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      awvalid <= '0;
    end
    else if (master_if.awvalid && master_if.awready) begin
      awvalid <= '0;
    end
    else if (slave_if.awvalid && slave_if.awready) begin
      awvalid <= '1;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      awid    <= '0;
      awaddr  <= '0;
      awprot  <= '0;
    end
    else if (slave_if.awvalid && slave_if.awready) begin
      awid    <= slave_if.awid;
      awaddr  <= slave_if.awaddr;
      awprot  <= slave_if.awprot;
    end
  end

  //  Write data channel
  always_comb begin
    slave_if.wready = !wvalid;
  end

  always_comb begin
    master_if.wvalid  = slave_if.wvalid || wvalid;
  end

  always_comb begin
    if (wvalid) begin
      master_if.wdata = wdata;
      master_if.wstrb = wstrb;
    end
    else begin
      master_if.wdata = slave_if.wdata;
      master_if.wstrb = slave_if.wstrb;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      wvalid  <= '0;
    end
    else if (master_if.wvalid && master_if.wready) begin
      wvalid  <= '0;
    end
    else if (slave_if.wvalid && slave_if.wready) begin
      wvalid  <= '1;
    end
  end

  always_ff @(posedge i_clk) begin
    if (slave_if.wvalid && slave_if.wready) begin
      wdata <= slave_if.wdata;
      wstrb <= slave_if.wstrb;
    end
  end

  //  Write response channel
  always_comb begin
    master_if.bready  = slave_if.bready;
    slave_if.bvalid   = master_if.bvalid;
    slave_if.bid      = master_if.bid;
    slave_if.bresp    = master_if.bresp;
  end

  //  Read address channel
  always_comb begin
    slave_if.arready  = !arvalid;
  end

  always_comb begin
    master_if.arvalid = slave_if.arvalid || arvalid;
  end

  always_comb begin
    if (arvalid) begin
      master_if.arid    = arid;
      master_if.araddr  = ADDRESS_WIDTH'(araddr);
      master_if.arprot  = arprot;
    end
    else begin
      master_if.arid    = slave_if.arid;
      master_if.araddr  = slave_if.araddr;
      master_if.arprot  = slave_if.arprot;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      arvalid <= '0;
    end
    else if (master_if.arvalid && master_if.arready) begin
      arvalid <= '0;
    end
    else if (slave_if.arvalid && slave_if.arready) begin
      arvalid <= '1;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      arid    <= '0;
      araddr  <= '0;
      arprot  <= '0;
    end
    else if (slave_if.arvalid && slave_if.arready) begin
      arid    <= slave_if.arid;
      araddr  <= slave_if.araddr;
      arprot  <= slave_if.arprot;
    end
  end

  //  Read response channel
  always_comb begin
    master_if.rready  = slave_if.rready;
    slave_if.rvalid   = master_if.rvalid;
    slave_if.rid      = master_if.rid;
    slave_if.rresp    = master_if.rresp;
    slave_if.rdata    = master_if.rdata;
  end
endmodule
