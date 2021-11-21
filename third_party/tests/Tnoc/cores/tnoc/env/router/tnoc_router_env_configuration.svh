`ifndef TNOC_ROUTER_ENV_CONFIGURATION_SVH
`define TNOC_ROUTER_ENV_CONFIGURATION_SVH
class tnoc_router_env_configuration extends tue_configuration;
  rand  tnoc_bfm_id_x           id_x;
  rand  tnoc_bfm_id_y           id_y;
  rand  int                     size_x;
  rand  int                     size_y;
  rand  tnoc_bfm_data           error_data;
  rand  tnoc_bfm_configuration  bfm_cfg[5];

  constraint c_default_id {
    foreach (bfm_cfg[i]) {
      if (i == 0) {
        soft bfm_cfg[i].id_x == (id_x + 1);
        soft bfm_cfg[i].id_y == (id_y + 0);
      }
      else if (i == 1) {
        soft bfm_cfg[i].id_x == (id_x - 1);
        soft bfm_cfg[i].id_y == (id_y + 0);
      }
      else if (i == 2) {
        soft bfm_cfg[i].id_x == (id_x + 0);
        soft bfm_cfg[i].id_y == (id_y + 1);
      }
      else if (i == 3) {
        soft bfm_cfg[i].id_x == (id_x + 0);
        soft bfm_cfg[i].id_y == (id_y - 1);
      }
      else if (i == 4) {
        soft bfm_cfg[i].id_x == (id_x + 0);
        soft bfm_cfg[i].id_y == (id_y + 0);
      }
    }
  }

  function new(string name = "tnoc_router_env_configuration");
    super.new(name);
    foreach (bfm_cfg[i]) begin
      bfm_cfg[i]  = tnoc_bfm_configuration::type_id::create($sformatf("bfm_cfg[%0d]", i));
    end
  endfunction

  `uvm_object_utils(tnoc_router_env_configuration)
endclass
`endif
