module top();
  timeunit  1ns/1ps;

  import  tnoc_pkg::*;
  import  tnoc_axi_pkg::*;
  import  uvm_pkg::*;
  import  tue_pkg::*;
  import  tnoc_bfm_pkg::*;
  import  tvip_axi_types_pkg::*;
  import  tvip_axi_pkg::*;
  import  tnoc_axi_adapter_env_pkg::*;
  import  tnoc_axi_adapter_tests_pkg::*;

  `ifndef TNOC_AXI_ADAPTER_ENV_PACKET_DATA_WIDTH
    `define TNOC_AXI_ADAPTER_ENV_PACKET_DATA_WIDTH  64
  `endif

  `ifndef TNOC_AXI_ADAPTER_ENV_DATA_WIDTH
    `define TNOC_AXI_ADAPTER_ENV_DATA_WIDTH `TNOC_AXI_ADAPTER_ENV_PACKET_DATA_WIDTH
  `endif

  localparam  int DATA_WIDTH        = `TNOC_AXI_ADAPTER_ENV_PACKET_DATA_WIDTH;
  localparam  int MAX_BURST_LENGTH  = 256;
  localparam  int MAX_BYTE_LENGTH   = 4096;

  localparam  tnoc_packet_config  PACKET_CONFIG = '{
    size_x:           3,
    size_y:           2,
    virtual_channels: 4,
    tags:             32,
    address_width:    TNOC_DEFAULT_PACKET_CONFIG.address_width,
    data_width:       `TNOC_AXI_ADAPTER_ENV_PACKET_DATA_WIDTH,
    max_data_width:   TNOC_DEFAULT_PACKET_CONFIG.max_data_width,
    max_byte_length:  MAX_BYTE_LENGTH
  };

  localparam  tnoc_axi_config AXI_CONFIG  = '{
    id_width:       $clog2(PACKET_CONFIG.tags),
    address_width:  PACKET_CONFIG.address_width,
    data_width:     `TNOC_AXI_ADAPTER_ENV_DATA_WIDTH,
    qos_width:      1
  };

  bit clk = 0;
  initial begin
    forever #(0.5ns) begin
      clk ^= 1;
    end
  end

  bit rst_n = 1;
  initial begin
    rst_n = 0;
    repeat (20) begin
      @(posedge clk);
    end
    rst_n = 1;
  end

//--------------------------------------------------------------
//  AXI VIP Connections
//--------------------------------------------------------------
  localparam  int MASTER_ID_X[3]  = '{0, 2, 1};
  localparam  int MASTER_ID_Y[3]  = '{0, 0, 1};
  localparam  int SLAVE_ID_X[3]   = '{1, 0, 2};
  localparam  int SLAVE_ID_Y[3]   = '{0, 1, 1};

  tvip_axi_if   axi_vip2dut_if[3](clk, rst_n);
  tvip_axi_if   axi_dut2vip_if[3](clk, rst_n);

  tvip_axi_vif  axi_master_vif[int][int];
  tvip_axi_vif  axi_slave_vif[int][int];

  for (genvar i = 0;i < 3;++i) begin
    initial begin
      axi_master_vif[MASTER_ID_Y[i]][MASTER_ID_X[i]]  = axi_vip2dut_if[i];
      axi_slave_vif[SLAVE_ID_Y[i]][SLAVE_ID_X[i]]     = axi_dut2vip_if[i];
    end
  end

//--------------------------------------------------------------
//  Flit IF Connections
//--------------------------------------------------------------
  tnoc_bfm_flit_vif flit_tx_vif[int][int];
  tnoc_bfm_flit_vif flit_rx_vif[int][int];

  for (genvar i = 0;i < 6;++i) begin
    for (genvar j = 0;j < PACKET_CONFIG.virtual_channels;++j) begin
      initial begin
        flit_tx_vif[i][j] = u_dut_wrapper.flit_tx_if[PACKET_CONFIG.virtual_channels*i+j];
        flit_rx_vif[i][j] = u_dut_wrapper.flit_rx_if[PACKET_CONFIG.virtual_channels*i+j];
      end
    end
  end

//--------------------------------------------------------------
//  DUT
//--------------------------------------------------------------
  tnoc_types #(PACKET_CONFIG)   packet_types();
  tnoc_axi_types #(AXI_CONFIG)  axi_types();

  tnoc_axi_adapter_dut_wrapper #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .AXI_CONFIG     (AXI_CONFIG     )
  ) u_dut_wrapper (
    .packet_types (packet_types   ),
    .axi_types    (axi_types      ),
    .i_clk        (clk            ),
    .i_rst_n      (rst_n          ),
    .slave_if     (axi_vip2dut_if ),
    .master_if    (axi_dut2vip_if )
  );

//--------------------------------------------------------------
//  UVM
//--------------------------------------------------------------
  function automatic tnoc_axi_adapter_env_configuration create_cfg();
    tnoc_axi_adapter_env_configuration  cfg = new();
    cfg.create_sub_cfgs(3, 2, flit_tx_vif, flit_rx_vif, axi_master_vif, axi_slave_vif);
    assert (cfg.randomize() with {
      foreach (axi_master_cfg[i]) {
        axi_master_cfg[i].id_width         == AXI_CONFIG.id_width;
        axi_master_cfg[i].address_width    == AXI_CONFIG.address_width;
        axi_master_cfg[i].max_burst_length == MAX_BURST_LENGTH;
        axi_master_cfg[i].qos_range[0]     == 0;
        axi_master_cfg[i].qos_range[1]     == (PACKET_CONFIG.virtual_channels - 1);
        axi_master_cfg[i].data_width       == AXI_CONFIG.data_width;

        axi_master_cfg[i].request_start_delay.min_delay          == 0;
        axi_master_cfg[i].request_start_delay.max_delay          == 10;
        axi_master_cfg[i].request_start_delay.weight_zero_delay  == 7;
        axi_master_cfg[i].request_start_delay.weight_short_delay == 2;
        axi_master_cfg[i].request_start_delay.weight_long_delay  == 1;

        axi_master_cfg[i].write_data_delay.min_delay          == 0;
        axi_master_cfg[i].write_data_delay.max_delay          == 10;
        axi_master_cfg[i].write_data_delay.weight_zero_delay  == 17;
        axi_master_cfg[i].write_data_delay.weight_short_delay == 2;
        axi_master_cfg[i].write_data_delay.weight_long_delay  == 1;

        axi_master_cfg[i].bready_delay.min_delay          == 0;
        axi_master_cfg[i].bready_delay.max_delay          == 10;
        axi_master_cfg[i].bready_delay.weight_zero_delay  == 7;
        axi_master_cfg[i].bready_delay.weight_short_delay == 2;
        axi_master_cfg[i].bready_delay.weight_long_delay  == 1;

        axi_master_cfg[i].rready_delay.min_delay          == 0;
        axi_master_cfg[i].rready_delay.max_delay          == 10;
        axi_master_cfg[i].rready_delay.weight_zero_delay  == 7;
        axi_master_cfg[i].rready_delay.weight_short_delay == 2;
        axi_master_cfg[i].rready_delay.weight_long_delay  == 1;
      }
      foreach (axi_slave_cfg[i]) {
        axi_slave_cfg[i].id_width         == AXI_CONFIG.id_width;
        axi_slave_cfg[i].address_width    == AXI_CONFIG.address_width;
        axi_slave_cfg[i].max_burst_length == MAX_BURST_LENGTH;
        axi_slave_cfg[i].data_width       == AXI_CONFIG.data_width;

        axi_slave_cfg[i].response_start_delay.min_delay          == 0;
        axi_slave_cfg[i].response_start_delay.max_delay          == 10;
        axi_slave_cfg[i].response_start_delay.weight_zero_delay  == 7;
        axi_slave_cfg[i].response_start_delay.weight_short_delay == 2;
        axi_slave_cfg[i].response_start_delay.weight_long_delay  == 1;

        axi_slave_cfg[i].response_delay.min_delay          == 0;
        axi_slave_cfg[i].response_delay.max_delay          == 10;
        axi_slave_cfg[i].response_delay.weight_zero_delay  == 17;
        axi_slave_cfg[i].response_delay.weight_short_delay == 2;
        axi_slave_cfg[i].response_delay.weight_long_delay  == 1;

        axi_slave_cfg[i].awready_delay.min_delay          == 0;
        axi_slave_cfg[i].awready_delay.max_delay          == 10;
        axi_slave_cfg[i].awready_delay.weight_zero_delay  == 7;
        axi_slave_cfg[i].awready_delay.weight_short_delay == 2;
        axi_slave_cfg[i].awready_delay.weight_long_delay  == 1;

        axi_slave_cfg[i].wready_delay.min_delay          == 0;
        axi_slave_cfg[i].wready_delay.max_delay          == 10;
        axi_slave_cfg[i].wready_delay.weight_zero_delay  == 7;
        axi_slave_cfg[i].wready_delay.weight_short_delay == 2;
        axi_slave_cfg[i].wready_delay.weight_long_delay  == 1;

        axi_slave_cfg[i].arready_delay.min_delay          == 0;
        axi_slave_cfg[i].arready_delay.max_delay          == 10;
        axi_slave_cfg[i].arready_delay.weight_zero_delay  == 7;
        axi_slave_cfg[i].arready_delay.weight_short_delay == 2;
        axi_slave_cfg[i].arready_delay.weight_long_delay  == 1;

        axi_slave_cfg[i].enable_response_interleaving == (i == 5);
        axi_slave_cfg[i].response_ordering            == TVIP_AXI_OUT_OF_ORDER;
        axi_slave_cfg[i].outstanding_responses inside {[4:32]};
      }
      foreach (fabric_env_cfg.bfm_cfg[i]) {
        fabric_env_cfg.bfm_cfg[i].agent_mode       == UVM_PASSIVE;
        fabric_env_cfg.bfm_cfg[i].id_x_width       == get_id_x_width(PACKET_CONFIG);
        fabric_env_cfg.bfm_cfg[i].id_y_width       == get_id_y_width(PACKET_CONFIG);
        fabric_env_cfg.bfm_cfg[i].virtual_channels == PACKET_CONFIG.virtual_channels;
        fabric_env_cfg.bfm_cfg[i].tags             == PACKET_CONFIG.tags;
        fabric_env_cfg.bfm_cfg[i].address_width    == PACKET_CONFIG.address_width;
        fabric_env_cfg.bfm_cfg[i].data_width       == PACKET_CONFIG.data_width;
        fabric_env_cfg.bfm_cfg[i].max_data_width   == PACKET_CONFIG.max_data_width;
        fabric_env_cfg.bfm_cfg[i].max_byte_length  == PACKET_CONFIG.max_byte_length;
      }
      fabric_env_cfg.error_data == ((1 << DATA_WIDTH) - 1);
    });
    return cfg;
  endfunction

  initial begin
    uvm_wait_for_nba_region();
    uvm_config_db #(tnoc_axi_adapter_env_configuration)::set(
      null, "", "configuration", create_cfg()
    );
    run_test();
  end
endmodule
