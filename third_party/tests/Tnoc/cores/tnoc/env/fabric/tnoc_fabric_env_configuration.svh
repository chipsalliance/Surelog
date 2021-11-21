`ifndef TNOC_FABRIC_ENV_CONFIGURATION_SVH
`define TNOC_FABRIC_ENV_CONFIGURATION_SVH
class tnoc_fabric_env_configuration extends tue_configuration;
        int                     size_x;
        int                     size_y;
  rand  tnoc_bfm_data           error_data;
  rand  tnoc_bfm_configuration  bfm_cfg[int];

  constraint c_default_id {
    foreach (bfm_cfg[i]) {
      soft bfm_cfg[i].id_x == (i % size_x);
      soft bfm_cfg[i].id_y == (i / size_x);
    }
  }

  function void create_sub_cfgs(
    input int               size_x,
    input int               size_y,
    ref   tnoc_bfm_flit_vif tx_vif[int][int],
    ref   tnoc_bfm_flit_vif rx_vif[int][int]
  );
    this.size_x = size_x;
    this.size_y = size_y;

    for (int i = 0;i < size_x * size_y;++i) begin
      int x = i % size_x;
      int y = i / size_y;
      bfm_cfg[i]  = tnoc_bfm_configuration::type_id::create($sformatf("bfm_cfg[%0d][%0d]", y, x));
      foreach (tx_vif[i][j]) begin
        bfm_cfg[i].tx_vif[j]  = tx_vif[i][j];
      end
      foreach (rx_vif[i][j]) begin
        bfm_cfg[i].rx_vif[j]  = rx_vif[i][j];
      end
    end
  endfunction

  function tnoc_bfm_configuration get_bfm_cfg(int y, int x);
    return bfm_cfg[size_x*y+x];
  endfunction

  `tue_object_default_constructor(tnoc_fabric_env_configuration)
  `uvm_object_utils(tnoc_fabric_env_configuration)
endclass
`endif
