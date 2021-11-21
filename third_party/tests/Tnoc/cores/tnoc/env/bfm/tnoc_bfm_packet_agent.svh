`ifndef TNOC_BFM_PACKET_AGENT_SVH
`define TNOC_BFM_PACKET_AGENT_SVH
typedef tue_agent #(
  .CONFIGURATION  (tnoc_bfm_configuration ),
  .STATUS         (tnoc_bfm_status        )
) tnoc_bfm_packet_agent_base;

class tnoc_bfm_packet_agent extends tnoc_bfm_packet_agent_base;
  uvm_analysis_port #(tnoc_bfm_packet_item) tx_packet_port;
  uvm_analysis_port #(tnoc_bfm_packet_item) rx_packet_port;

  tnoc_bfm_packet_sequencer sequencer;
  tnoc_bfm_packet_vc_agent  vc_agent[int];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    tx_packet_port  = new("tx_packet_port", this);
    rx_packet_port  = new("rx_packet_port", this);

    if (is_active_agent()) begin
      sequencer = tnoc_bfm_packet_sequencer::type_id::create("sequencer", this);
      sequencer.set_context(configuration, status);
    end

    foreach (configuration.tx_vif[vc]) begin
      create_vc_agent(vc);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    foreach (vc_agent[vc]) begin
      vc_agent[vc].tx_packet_port.connect(tx_packet_port);
      vc_agent[vc].rx_packet_port.connect(rx_packet_port);
      if (is_active_agent()) begin
        sequencer.connect_vc_agent(vc_agent[vc]);
      end
    end
  endfunction

  function void apply_agent_mode();
    case (configuration.agent_mode)
      UVM_ACTIVE:   active_agent();
      UVM_PASSIVE:  passive_agent();
    endcase
  endfunction

  function void create_vc_agent(int vc);
    vc_agent[vc]    = tnoc_bfm_packet_vc_agent::type_id::create($sformatf("vc_agent[%0d]", vc), this);
    vc_agent[vc].vc = vc;
    vc_agent[vc].set_configuration(configuration);
    if (is_passive_agent()) begin
      vc_agent[vc].passive_agent();
    end
  endfunction

  `tue_component_default_constructor(tnoc_bfm_packet_agent)
  `uvm_component_utils(tnoc_bfm_packet_agent)
endclass
`endif
