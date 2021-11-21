`ifndef TNOC_FABRIC_ENV_SEQUENCER_SVH
`define TNOC_FABRIC_ENV_SEQUENCER_SVH
class tnoc_fabric_env_sequencer extends tue_sequencer #(tnoc_fabric_env_configuration);
  tnoc_bfm_packet_sequencer bfm_sequencer[int][int];
  `tue_component_default_constructor(tnoc_fabric_env_sequencer)
  `uvm_component_utils(tnoc_fabric_env_sequencer)
endclass
`endif
