module top();
  timeunit  1ns/1ps;

  import  uvm_pkg::*;
  import  tue_pkg::*;
  import  tnoc_pkg::*;
  import  tnoc_bfm_types_pkg::*;
  import  tnoc_bfm_pkg::*;
  import  tnoc_common_env_pkg::*;
  import  tnoc_router_env_pkg::*;
  import  tnoc_router_tests_pkg::*;

  `ifndef TNOC_ROUTER_ENV_DATA_WIDTH
    `define TNOC_ROUTER_ENV_DATA_WIDTH TNOC_DEFAULT_PACKET_CONFIG.data_width
  `endif

  `ifndef TNOC_ROUTER_ENV_VIRTUAL_CHANNELS
    `define TNOC_ROUTER_ENV_VIRTUAL_CHANNELS  TNOC_DEFAULT_PACKET_CONFIG.virtual_channels
  `endif

  localparam  tnoc_packet_config  PACKET_CONFIG  = '{
    size_x:           TNOC_DEFAULT_PACKET_CONFIG.size_x,
    size_y:           TNOC_DEFAULT_PACKET_CONFIG.size_y,
    virtual_channels: `TNOC_ROUTER_ENV_VIRTUAL_CHANNELS,
    tags:             TNOC_DEFAULT_PACKET_CONFIG.tags,
    address_width:    TNOC_DEFAULT_PACKET_CONFIG.address_width,
    data_width:       `TNOC_ROUTER_ENV_DATA_WIDTH,
    max_data_width:   TNOC_DEFAULT_PACKET_CONFIG.max_data_width,
    max_byte_length:  TNOC_DEFAULT_PACKET_CONFIG.max_byte_length
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
    #(20ns);
    rst_n = 1;
  end

  tnoc_types #(PACKET_CONFIG)                                                   types();
  tnoc_flit_if #(.PACKET_CONFIG(PACKET_CONFIG), .PORT_TYPE(TNOC_INTERNAL_PORT)) internal_if[8](types);
  tnoc_flit_if #(.PACKET_CONFIG(PACKET_CONFIG), .PORT_TYPE(TNOC_LOCAL_PORT))    local_if[2](types);

  localparam  int CHANNELS  = PACKET_CONFIG.virtual_channels;
  tnoc_bfm_flit_if  bfm_if[10*CHANNELS](clk, rst_n);

  for (genvar i = 0;i < 4;++i) begin : g_internal_port
    always_comb begin
      internal_if[2*i+1].ready    = '1;
      internal_if[2*i+1].vc_ready = '1;
    end

    tnoc_bfm_flit_if_connector #(
      .PACKET_CONFIG  (PACKET_CONFIG      ),
      .PORT_TYPE      (TNOC_INTERNAL_PORT ),
      .MONITOR_MODE   (0                  )
    ) u_connector_bfm_to_dut (
      .types    (types                                        ),
      .i_clk    (clk                                          ),
      .i_rst_n  (rst_n                                        ),
      .dut_if   (internal_if[2*i+0]                           ),
      .bfm_if   (bfm_if[(2*i+0)*CHANNELS:(2*i+1)*CHANNELS-1]  )
    );

    tnoc_bfm_flit_if_connector #(
      .PACKET_CONFIG  (PACKET_CONFIG      ),
      .PORT_TYPE      (TNOC_INTERNAL_PORT ),
      .MONITOR_MODE   (1                  )
    ) u_connector_dut_to_bfm (
      .types    (types                                        ),
      .i_clk    (clk                                          ),
      .i_rst_n  (rst_n                                        ),
      .dut_if   (internal_if[2*i+1]                           ),
      .bfm_if   (bfm_if[(2*i+1)*CHANNELS:(2*i+2)*CHANNELS-1]  )
    );
  end

  if (1) begin : g_local_port
    always_comb begin
      local_if[1].ready     = '1;
      local_if[1].vc_ready  = '1;
    end

    tnoc_bfm_flit_if_connector #(
      .PACKET_CONFIG  (PACKET_CONFIG    ),
      .PORT_TYPE      (TNOC_LOCAL_PORT  ),
      .MONITOR_MODE   (0                )
    ) u_connector_bfm_to_dut (
      .types    (types                            ),
      .i_clk    (clk                              ),
      .i_rst_n  (rst_n                            ),
      .dut_if   (local_if[0]                      ),
      .bfm_if   (bfm_if[8*CHANNELS:9*CHANNELS-1]  )
    );

    tnoc_bfm_flit_if_connector #(
      .PACKET_CONFIG  (PACKET_CONFIG    ),
      .PORT_TYPE      (TNOC_LOCAL_PORT  ),
      .MONITOR_MODE   (1                )
    ) u_connector_dut_to_bfm (
      .types    (types                            ),
      .i_clk    (clk                              ),
      .i_rst_n  (rst_n                            ),
      .dut_if   (local_if[1]                      ),
      .bfm_if   (bfm_if[9*CHANNELS:10*CHANNELS-1] )
    );
  end

  virtual tnoc_bfm_flit_if  bfm_flit_in_vif[int][int];
  virtual tnoc_bfm_flit_if  bfm_flit_out_vif[int][int];

  for (genvar i = 0;i < 5;++i) begin
    for (genvar j = 0;j < CHANNELS;++j) begin
      initial begin
        bfm_flit_out_vif[i][j]  = bfm_if[CHANNELS*(2*i+0)+j];
        bfm_flit_in_vif[i][j]   = bfm_if[CHANNELS*(2*i+1)+j];
      end
    end
  end

  localparam  bit [get_id_x_width(PACKET_CONFIG)-1:0] ID_X  = 1;
  localparam  bit [get_id_y_width(PACKET_CONFIG)-1:0] ID_Y  = 1;
  tnoc_router #(
    .PACKET_CONFIG  (PACKET_CONFIG  )
  ) u_dut (
    .types              (types              ),
    .i_clk              (clk                ),
    .i_rst_n            (rst_n              ),
    .i_id_x             (ID_X               ),
    .i_id_y             (ID_Y               ),
    .receiver_if_xp     (internal_if[2*0+0] ),
    .sender_if_xp       (internal_if[2*0+1] ),
    .receiver_if_xm     (internal_if[2*1+0] ),
    .sender_if_xm       (internal_if[2*1+1] ),
    .receiver_if_yp     (internal_if[2*2+0] ),
    .sender_if_yp       (internal_if[2*2+1] ),
    .receiver_if_ym     (internal_if[2*3+0] ),
    .sender_if_ym       (internal_if[2*3+1] ),
    .receiver_if_local  (local_if[0]        ),
    .sender_if_local    (local_if[1]        )
  );

  task run();
    tnoc_router_env_configuration cfg = new();
    assert(cfg.randomize() with {
      id_x       == 1;
      id_y       == 1;
      size_x     == PACKET_CONFIG.size_x;
      size_y     == PACKET_CONFIG.size_y;
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

    for (int i = 0;i < 5;++i) begin
      for (int j = 0;j < CHANNELS;++j) begin
        cfg.bfm_cfg[i].tx_vif[j]  = bfm_flit_out_vif[i][j];
        cfg.bfm_cfg[i].rx_vif[j]  = bfm_flit_in_vif[i][j];
      end
    end

    uvm_config_db #(tnoc_router_env_configuration)::set(null, "", "configuration", cfg);
    run_test();
  endtask

  initial begin
    uvm_wait_for_nba_region();
    run();
  end
endmodule
