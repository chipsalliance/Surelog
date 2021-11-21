module tnoc_axi_adapter_dut_wrapper
  import  tnoc_pkg::*,
          tnoc_axi_pkg::*,
          tvip_axi_types_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter tnoc_axi_config     AXI_CONFIG    = TNOC_DEFAULT_AXI_CONFIG
)(
  tnoc_types      packet_types,
  tnoc_axi_types  axi_types,
  input logic     i_clk,
  input logic     i_rst_n,
  tvip_axi_if     slave_if[3],
  tvip_axi_if     master_if[3]
);
  typedef packet_types.tnoc_vc            tnoc_vc;
  typedef packet_types.tnoc_address       tnoc_address;
  typedef packet_types.tnoc_decode_result tnoc_decode_result;

  localparam  int ADDRESS_WIDTH = PACKET_CONFIG.address_width;
  localparam  int CHANNELS      = PACKET_CONFIG.virtual_channels;
  localparam  int ID_X_WIDTH    = get_id_x_width(PACKET_CONFIG);
  localparam  int ID_Y_WIDTH    = get_id_y_width(PACKET_CONFIG);

  localparam  int BFM_IFS = 6 * CHANNELS;
  tnoc_bfm_flit_if  flit_tx_if[BFM_IFS](i_clk, i_rst_n);
  tnoc_bfm_flit_if  flit_rx_if[BFM_IFS](i_clk, i_rst_n);

  tnoc_flit_if #(PACKET_CONFIG) flit_f2a_if[6](packet_types);
  tnoc_flit_if #(PACKET_CONFIG) flit_a2f_if[6](packet_types);

  for (genvar i = 0;i < 6;++i) begin : g_connector
    tnoc_bfm_flit_if_connector #(
      .PACKET_CONFIG  (PACKET_CONFIG    ),
      .PORT_TYPE      (TNOC_LOCAL_PORT  ),
      .MONITOR_MODE   (1                )
    ) u_connector_a2f (
      .types    (packet_types                             ),
      .i_clk    (i_clk                                    ),
      .i_rst_n  (i_rst_n                                  ),
      .dut_if   (flit_a2f_if[i]                           ),
      .bfm_if   (flit_tx_if[CHANNELS*i:CHANNELS*(i+1)-1]  )
    );

    tnoc_bfm_flit_if_connector #(
      .PACKET_CONFIG  (PACKET_CONFIG    ),
      .PORT_TYPE      (TNOC_LOCAL_PORT  ),
      .MONITOR_MODE   (1                )
    ) u_connector_f2a (
      .types    (packet_types                             ),
      .i_clk    (i_clk                                    ),
      .i_rst_n  (i_rst_n                                  ),
      .dut_if   (flit_f2a_if[i]                           ),
      .bfm_if   (flit_rx_if[CHANNELS*i:CHANNELS*(i+1)-1]  )
    );
  end

  function automatic tnoc_decode_result decode_address(tnoc_address address);
    tnoc_decode_result  result;
    case (address[ADDRESS_WIDTH-1:ADDRESS_WIDTH-2])
      0: begin
        result.id           = '{ x: 1, y: 0 };
        result.decode_error = 0;
      end
      1: begin
        result.id           = '{ x: 0, y: 1 };
        result.decode_error = 0;
      end
      2: begin
        result.id           = '{ x: 2, y: 1 };
        result.decode_error = 0;
      end
      3: begin
        bit decode_error;
        int id_x;
        int max_id_x;
        int id_y;
        decode_error  = $urandom_range(0, 1);
        max_id_x      = 2**ID_X_WIDTH - 1;
        void'(std::randomize(id_x, id_y) with {
          id_y inside {[0:1]};
          if (decode_error) {
            id_x inside {[0:2]};
          }
          else {
            id_x inside {[3:max_id_x]};
          }
        });
        result.id           = '{ x: id_x, y: id_y };
        result.decode_error = decode_error;
      end
    endcase
    return result;
  endfunction

  tnoc_vc base_vc[2];
  always_comb begin
    void'(std::randomize(base_vc) with {
      base_vc[0] != base_vc[1];
      foreach (base_vc[i]) {
        base_vc[i] inside {0, 1};
      }
    });
  end

  for (genvar i = 0;i < 3;++i) begin : g_slave_adapter
    localparam  int ID_X      = (i == 0) ? 0
                              : (i == 1) ? 2 : 1;
    localparam  int ID_Y      = (i == 0) ? 0
                              : (i == 1) ? 0 : 1;
    localparam  int IF_INDEX  = 3 * ID_Y + ID_X;

    tnoc_axi_if #(AXI_CONFIG)                 axi_if(axi_types);
    tnoc_address_decoder_if #(PACKET_CONFIG)  decoder_if[2](packet_types);
    tnoc_decode_result  [1:0]                 decode_result;

    always_comb begin
      decode_result[0]            = decode_address(decoder_if[0].address);
      decoder_if[0].id_x          = decode_result[0].id.x;
      decoder_if[0].id_y          = decode_result[0].id.y;
      decoder_if[0].decode_error  = decode_result[0].decode_error;
    end

    always_comb begin
      decode_result[1]            = decode_address(decoder_if[1].address);
      decoder_if[1].id_x          = decode_result[1].id.x;
      decoder_if[1].id_y          = decode_result[1].id.y;
      decoder_if[1].decode_error  = decode_result[1].decode_error;
    end

    always_comb begin
      axi_if.awvalid      = slave_if[i].awvalid;
      slave_if[i].awready = axi_if.awready;
      axi_if.awid         = slave_if[i].awid;
      axi_if.awaddr       = slave_if[i].awaddr;
      axi_if.awlen        = slave_if[i].awlen;
      axi_if.awsize       = tnoc_axi_burst_size'(slave_if[i].awsize);
      axi_if.awburst      = tnoc_axi_burst_type'(slave_if[i].awburst);
      axi_if.awqos        = slave_if[i].awqos;
    end

    always_comb begin
      axi_if.wvalid       = slave_if[i].wvalid;
      slave_if[i].wready  = axi_if.wready;
      axi_if.wdata        = slave_if[i].wdata;
      axi_if.wstrb        = slave_if[i].wstrb;
      axi_if.wlast        = slave_if[i].wlast;
    end

    always_comb begin
      slave_if[i].bvalid  = axi_if.bvalid;
      axi_if.bready       = slave_if[i].bready;
      slave_if[i].bid     = axi_if.bid;
      slave_if[i].bresp   = tvip_axi_response'(axi_if.bresp);
    end

    always_comb begin
      axi_if.arvalid      = slave_if[i].arvalid;
      slave_if[i].arready = axi_if.arready;
      axi_if.arid         = slave_if[i].arid;
      axi_if.araddr       = slave_if[i].araddr;
      axi_if.arlen        = slave_if[i].arlen;
      axi_if.arsize       = tnoc_axi_burst_size'(slave_if[i].arsize);
      axi_if.arburst      = tnoc_axi_burst_type'(slave_if[i].arburst);
      axi_if.arqos        = slave_if[i].arqos;
    end

    always_comb begin
      slave_if[i].rvalid  = axi_if.rvalid;
      axi_if.rready       = slave_if[i].rready;
      slave_if[i].rid     = axi_if.rid;
      slave_if[i].rdata   = axi_if.rdata;
      slave_if[i].rresp   = tvip_axi_response'(axi_if.rresp);
      slave_if[i].rlast   = axi_if.rlast;
    end

    tnoc_axi_slave_adapter #(
      .PACKET_CONFIG  (PACKET_CONFIG  ),
      .AXI_CONFIG     (AXI_CONFIG     )
    ) u_adapter (
      .packet_types       (packet_types           ),
      .axi_types          (axi_types              ),
      .i_clk              (i_clk                  ),
      .i_rst_n            (i_rst_n                ),
      .i_id_x             (ID_X[ID_X_WIDTH-1:0]   ),
      .i_id_y             (ID_Y[ID_Y_WIDTH-1:0]   ),
      .i_request_base_vc  (base_vc[0]             ),
      .write_decoder_if   (decoder_if[0]          ),
      .read_decoder_if    (decoder_if[1]          ),
      .axi_if             (axi_if                 ),
      .receiver_if        (flit_f2a_if[IF_INDEX]  ),
      .sender_if          (flit_a2f_if[IF_INDEX]  )
    );
  end

  for (genvar i = 0;i < 3;++i) begin : g_master_adapter
    localparam  int ID_X      = (i == 0) ? 1
                              : (i == 1) ? 0 : 2;
    localparam  int ID_Y      = (i == 0) ? 0
                              : (i == 1) ? 1 : 1;
    localparam  int IF_INDEX  = 3 * ID_Y + ID_X;

    tnoc_axi_if #(AXI_CONFIG) axi_if(axi_types);

    always_comb begin
      master_if[i].awvalid  = axi_if.awvalid;
      axi_if.awready        = master_if[i].awready;
      master_if[i].awid     = axi_if.awid;
      master_if[i].awaddr   = axi_if.awaddr;
      master_if[i].awlen    = axi_if.awlen;
      master_if[i].awsize   = tvip_axi_burst_size'(axi_if.awsize);
      master_if[i].awburst  = tvip_axi_burst_type'(axi_if.awburst);
      master_if[i].awqos    = axi_if.awqos;
    end

    always_comb begin
      master_if[i].wvalid = axi_if.wvalid;
      axi_if.wready       = master_if[i].wready;
      master_if[i].wdata  = axi_if.wdata;
      master_if[i].wstrb  = axi_if.wstrb;
      master_if[i].wlast  = axi_if.wlast;
    end

    always_comb begin
      axi_if.bvalid       = master_if[i].bvalid;
      master_if[i].bready = axi_if.bready;
      axi_if.bid          = master_if[i].bid;
      axi_if.bresp        = tnoc_axi_response'(master_if[i].bresp);
    end

    always_comb begin
      master_if[i].arvalid  = axi_if.arvalid;
      axi_if.arready        = master_if[i].arready;
      master_if[i].arid     = axi_if.arid;
      master_if[i].araddr   = axi_if.araddr;
      master_if[i].arlen    = axi_if.arlen;
      master_if[i].arsize   = tvip_axi_burst_size'(axi_if.arsize);
      master_if[i].arburst  = tvip_axi_burst_type'(axi_if.arburst);
      master_if[i].arqos    = axi_if.arqos;
    end

    always_comb begin
      axi_if.rvalid       = master_if[i].rvalid;
      master_if[i].rready = axi_if.rready;
      axi_if.rid          = master_if[i].rid;
      axi_if.rdata        = master_if[i].rdata;
      axi_if.rresp        = tnoc_axi_response'(master_if[i].rresp);
      axi_if.rlast        = master_if[i].rlast;
    end

    tnoc_axi_master_adapter #(
      .PACKET_CONFIG  (PACKET_CONFIG  ),
      .AXI_CONFIG     (AXI_CONFIG     )
    ) u_adapter (
      .packet_types       (packet_types           ),
      .axi_types          (axi_types              ),
      .i_clk              (i_clk                  ),
      .i_rst_n            (i_rst_n                ),
      .i_id_x             (ID_X[ID_X_WIDTH-1:0]   ),
      .i_id_y             (ID_Y[ID_Y_WIDTH-1:0]   ),
      .i_response_base_vc (base_vc[1]             ),
      .axi_if             (axi_if                 ),
      .receiver_if        (flit_f2a_if[IF_INDEX]  ),
      .sender_if          (flit_a2f_if[IF_INDEX]  )
    );
  end

  tnoc_fabric #(PACKET_CONFIG) u_fabric (
    .types        (packet_types ),
    .i_clk        (i_clk        ),
    .i_rst_n      (i_rst_n      ),
    .receiver_if  (flit_a2f_if  ),
    .sender_if    (flit_f2a_if  )
  );
endmodule
