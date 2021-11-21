`ifndef TNOC_FABRIC_ENV_SVH
`define TNOC_FABRIC_ENV_SVH
class tnoc_fabric_env extends tue_env #(tnoc_fabric_env_configuration);
  tnoc_bfm_packet_agent     bfm_agent[int][int];
  tnoc_packet_scoreboard    packet_scoreboard[int][int];
  tnoc_fabric_env_model     model;
  tnoc_fabric_env_sequencer sequencer;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    for (int y = 0;y < configuration.size_y;++y) begin
      for (int x = 0;x < configuration.size_x;++x) begin
        bfm_agent[y][x] = tnoc_bfm_packet_agent::type_id::create($sformatf("bfm_agent[%0d][%0d]", y, x), this);
        bfm_agent[y][x].set_configuration(configuration.get_bfm_cfg(y, x));

        packet_scoreboard[y][x] = tnoc_packet_scoreboard::type_id::create($sformatf("packet_scoreboard[%0d][%0d]", y, x), this);
        packet_scoreboard[y][x].set_configuration(configuration.get_bfm_cfg(y, x));
      end
    end

    model = tnoc_fabric_env_model::type_id::create("model", this);
    model.set_configuration(configuration);

    sequencer = tnoc_fabric_env_sequencer::type_id::create("sequencer", this);
    sequencer.set_configuration(configuration);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    foreach (bfm_agent[y, x]) begin
      bfm_agent[y][x].tx_packet_port.connect(model.packet_export);
      bfm_agent[y][x].rx_packet_port.connect(packet_scoreboard[y][x].rx_packet_export);
      model.packet_port[y][x].connect(packet_scoreboard[y][x].tx_packet_export);
      sequencer.bfm_sequencer[y][x] = bfm_agent[y][x].sequencer;
    end
  endfunction

  `tue_component_default_constructor(tnoc_fabric_env)
  `uvm_component_utils(tnoc_fabric_env)
endclass
`endif
