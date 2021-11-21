`ifndef TNOC_ROUTER_ENV_SVH
`define TNOC_ROUTER_ENV_SVH
class tnoc_router_env extends tue_env #(tnoc_router_env_configuration);
  tnoc_bfm_packet_agent     bfm_agent[5];
  tnoc_packet_scoreboard    packet_scoreboard[5];
  tnoc_router_env_model     model;
  tnoc_router_env_sequencer sequencer;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    foreach (bfm_agent[i]) begin
      bfm_agent[i]  = tnoc_bfm_packet_agent::type_id::create($sformatf("bfm_agent[%0d]", i), this);
      bfm_agent[i].set_configuration(configuration.bfm_cfg[i]);

      packet_scoreboard[i]  = tnoc_packet_scoreboard::type_id::create($sformatf("packet_scoreboard[%0d]", i), this);
      packet_scoreboard[i].set_configuration(configuration.bfm_cfg[i]);
    end

    model = tnoc_router_env_model::type_id::create("model", this);
    model.set_configuration(configuration);

    sequencer = tnoc_router_env_sequencer::type_id::create("sequencer", this);
    sequencer.set_configuration(configuration);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    foreach (bfm_agent[i]) begin
      bfm_agent[i].tx_packet_port.connect(model.packet_export);
      bfm_agent[i].rx_packet_port.connect(packet_scoreboard[i].rx_packet_export);
      model.packet_port[i].connect(packet_scoreboard[i].tx_packet_export);
      sequencer.bfm_sequencer[i] = bfm_agent[i].sequencer;
    end
  endfunction

  `tue_component_default_constructor(tnoc_router_env)
  `uvm_component_utils(tnoc_router_env)
endclass
`endif
