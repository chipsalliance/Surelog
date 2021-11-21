`ifndef TNOC_AXI_ADAPTER_ENV_CONFIGURATION_SVH
`define TNOC_AXI_ADAPTER_ENV_CONFIGURATION_SVH
class tnoc_axi_adapter_env_configuration extends tue_configuration;
        int                           size_x;
        int                           size_y;
  rand  tnoc_fabric_env_configuration fabric_env_cfg;
  rand  tvip_axi_configuration        axi_master_cfg[int];
  rand  tvip_axi_configuration        axi_slave_cfg[int];

  function void create_sub_cfgs(
    input int               size_x,
    input int               size_y,
    ref   tnoc_bfm_flit_vif flit_tx_vif[int][int],
    ref   tnoc_bfm_flit_vif flit_rx_vif[int][int],
    ref   tvip_axi_vif      axi_master_vif[int][int],
    ref   tvip_axi_vif      axi_slave_vif[int][int]
  );
    this.size_x = size_x;
    this.size_y = size_y;

    fabric_env_cfg  = tnoc_fabric_env_configuration::type_id::create("fabric_cfg");
    fabric_env_cfg.create_sub_cfgs(size_x, size_y, flit_tx_vif, flit_rx_vif);

    foreach (axi_master_vif[i, j]) begin
      int index = size_x * i + j;
      axi_master_cfg[index]     = tvip_axi_configuration::type_id::create($sformatf("axi_master_cfg[%0d][%0d]", i, j));
      axi_master_cfg[index].vif = axi_master_vif[i][j];
    end

    foreach (axi_slave_vif[i, j]) begin
      int index = size_x * i + j;
      axi_slave_cfg[index]      = tvip_axi_configuration::type_id::create($sformatf("axi_slave_cfg[%0d][%0d]", i, j));
      axi_slave_cfg[index].vif  = axi_slave_vif[i][j];
    end
  endfunction

  function tvip_axi_configuration get_axi_master_cfg(int y, int x);
    int index = size_x * y + x;
    if (axi_master_cfg.exists(index)) begin
      return axi_master_cfg[index];
    end
    else begin
      return null;
    end
  endfunction

  function tvip_axi_configuration get_axi_slave_cfg(int y, int x);
    int index = size_x * y + x;
    if (axi_slave_cfg.exists(index)) begin
      return axi_slave_cfg[index];
    end
    else begin
      return null;
    end
  endfunction

  `tue_object_default_constructor(tnoc_axi_adapter_env_configuration)
  `uvm_object_utils(tnoc_axi_adapter_env_configuration)
endclass
`endif
