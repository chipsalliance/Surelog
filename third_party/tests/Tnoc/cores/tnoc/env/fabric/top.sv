module top();
  timeunit  1ns/1ps;

  import  uvm_pkg::*;
  import  tue_pkg::*;
  import  tnoc_pkg::*;
  import  tnoc_bfm_types_pkg::*;
  import  tnoc_bfm_pkg::*;
  import  tnoc_common_env_pkg::*;
  import  tnoc_fabric_env_pkg::*;
  import  tnoc_fabric_tests_pkg::*;

  `ifndef TNOC_FABRIC_ENV_DATA_WIDTH
    `define TNOC_FABRIC_ENV_DATA_WIDTH TNOC_DEFAULT_PACKET_CONFIG.data_width
  `endif

  `ifndef TNOC_ROUTER_ENV_VIRTUAL_CHANNELS
    `define TNOC_ROUTER_ENV_VIRTUAL_CHANNELS  TNOC_DEFAULT_PACKET_CONFIG.virtual_channels
  `endif

  localparam  tnoc_packet_config  PACKET_CONFIG = '{
    size_x:           TNOC_DEFAULT_PACKET_CONFIG.size_x,
    size_y:           TNOC_DEFAULT_PACKET_CONFIG.size_y,
    virtual_channels: `TNOC_ROUTER_ENV_VIRTUAL_CHANNELS,
    tags:             TNOC_DEFAULT_PACKET_CONFIG.tags,
    address_width:    TNOC_DEFAULT_PACKET_CONFIG.address_width,
    data_width:       `TNOC_FABRIC_ENV_DATA_WIDTH,
    max_data_width:   TNOC_DEFAULT_PACKET_CONFIG.max_data_width,
    max_byte_length:  TNOC_DEFAULT_PACKET_CONFIG.max_byte_length
  };

  localparam  int CHANNELS  = PACKET_CONFIG.virtual_channels;

  bit clk = 0;
  initial begin
    forever #(0.5ns) begin
      clk ^= 1;
    end
  end

  bit rst_n = 1;
  initial begin
    rst_n = 0;
    #(20ns);
    rst_n = 1;
  end

  tnoc_types #(PACKET_CONFIG)   types();
  tnoc_flit_if #(PACKET_CONFIG) flit_if_b2d[9](types);
  tnoc_flit_if #(PACKET_CONFIG) flit_if_d2b[9](types);

  tnoc_bfm_flit_if  bfm_flit_if_b2d[9*CHANNELS](clk, rst_n);
  tnoc_bfm_flit_if  bfm_flit_if_d2b[9*CHANNELS](clk, rst_n);

  for (genvar i = 0;i < 9;++i) begin : g_connector
    assign  flit_if_d2b[i].ready    = '1;
    assign  flit_if_d2b[i].vc_ready = '1;

    tnoc_bfm_flit_if_connector #(
      .PACKET_CONFIG  (PACKET_CONFIG    ),
      .PORT_TYPE      (TNOC_LOCAL_PORT  ),
      .MONITOR_MODE   (0                )
    ) u_connector_bfm_to_dut (
      .types    (types                                                  ),
      .i_clk    (clk                                                    ),
      .i_rst_n  (rst_n                                                  ),
      .dut_if   (flit_if_b2d[i]                                         ),
      .bfm_if   (bfm_flit_if_b2d[CHANNELS*i:CHANNELS*(i+1)-1].initiator )
    );

    tnoc_bfm_flit_if_connector #(
      .PACKET_CONFIG  (PACKET_CONFIG    ),
      .PORT_TYPE      (TNOC_LOCAL_PORT  ),
      .MONITOR_MODE   (1                )
    ) u_connector_dut_to_bfm (
      .types    (types                                                ),
      .i_clk    (clk                                                  ),
      .i_rst_n  (rst_n                                                ),
      .dut_if   (flit_if_d2b[i]                                       ),
      .bfm_if   (bfm_flit_if_d2b[CHANNELS*i:CHANNELS*(i+1)-1].monitor )
    );
  end

  tnoc_bfm_flit_vif tx_vif[int][int];
  tnoc_bfm_flit_vif rx_vif[int][int];

  for (genvar i = 0;i < 9;++i) begin
    for (genvar j = 0;j < CHANNELS;++j) begin
      initial begin
        tx_vif[i][j]  = bfm_flit_if_b2d[CHANNELS*i+j];
        rx_vif[i][j]  = bfm_flit_if_d2b[CHANNELS*i+j];
      end
    end
  end

  tnoc_fabric #(PACKET_CONFIG) u_dut (
    .types        (types        ),
    .i_clk        (clk          ),
    .i_rst_n      (rst_n        ),
    .receiver_if  (flit_if_b2d  ),
    .sender_if    (flit_if_d2b  )
  );

  function automatic tnoc_fabric_env_configuration create_cfg();
    tnoc_fabric_env_configuration cfg = new();
    cfg.create_sub_cfgs(
      PACKET_CONFIG.size_x, PACKET_CONFIG.size_y, tx_vif, rx_vif
    );
    assert(cfg.randomize() with {
      error_data == ((1 << PACKET_CONFIG.data_width) - 1);
      foreach (bfm_cfg[i]) {
        bfm_cfg[i].id_x_width       == get_id_x_width(PACKET_CONFIG);
        bfm_cfg[i].id_y_width       == get_id_y_width(PACKET_CONFIG);
        bfm_cfg[i].virtual_channels == PACKET_CONFIG.virtual_channels;
        bfm_cfg[i].tags             == PACKET_CONFIG.tags;
        bfm_cfg[i].address_width    == PACKET_CONFIG.address_width;
        bfm_cfg[i].data_width       == PACKET_CONFIG.data_width;
        bfm_cfg[i].max_data_width   == PACKET_CONFIG.max_data_width;
        bfm_cfg[i].max_byte_length  == PACKET_CONFIG.max_byte_length;
      }
    });
    return cfg;
  endfunction

  initial begin
    uvm_wait_for_nba_region();
    uvm_config_db #(tnoc_fabric_env_configuration)::set(null, "", "configuration", create_cfg());
    run_test();
  end
endmodule
