`ifndef TNOC_ROUTER_ENV_SEQUENCER_SVH
`define TNOC_ROUTER_ENV_SEQUENCER_SVH
class tnoc_router_env_sequencer extends tue_sequencer #(tnoc_router_env_configuration);
  tnoc_bfm_packet_sequencer bfm_sequencer[5];
  `tue_component_default_constructor(tnoc_router_env_sequencer)
  `uvm_component_utils(tnoc_router_env_sequencer)
endclass
`endif
