`ifndef TNOC_AXI_ADAPTER_ENV_SEQUENCER_SVH
`define TNOC_AXI_ADAPTER_ENV_SEQUENCER_SVH
class tnoc_axi_adapter_env_sequencer extends tue_sequencer #(tnoc_axi_adapter_env_configuration);
  tvip_axi_master_sequencer axi_master_sequencer[int][int];
  tvip_axi_slave_sequencer  axi_slave_sequencer[int][int];
  `tue_component_default_constructor(tnoc_axi_adapter_env_sequencer)
  `uvm_component_utils(tnoc_axi_adapter_env_sequencer)
endclass
`endif
