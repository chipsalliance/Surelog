`ifndef TNOC_BFM_PACKET_VC_AGENT_SVH
`define TNOC_BFM_PACKET_VC_AGENT_SVH

typedef tue_param_agent #(
  .CONFIGURATION  (tnoc_bfm_configuration       ),
  .STATUS         (tnoc_bfm_status              ),
  .SEQUENCER      (tnoc_bfm_packet_vc_sequencer ),
  .DRIVER         (tnoc_bfm_packet_vc_driver    )
) tnoc_bfm_packet_vc_agent_base;

class tnoc_bfm_packet_vc_agent extends tnoc_bfm_packet_vc_agent_base;
  uvm_analysis_port #(tnoc_bfm_packet_item) tx_packet_port;
  uvm_analysis_port #(tnoc_bfm_packet_item) rx_packet_port;

  int                           vc;
  tnoc_bfm_packet_tx_vc_monitor tx_monitor;
  tnoc_bfm_packet_rx_vc_monitor rx_monitor;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (is_active_agent()) begin
      sequencer.vc  = vc;
      driver.vc     = vc;
    end

    tx_packet_port  = new("tx_packet_port", this);
    tx_monitor      = tnoc_bfm_packet_tx_vc_monitor::type_id::create("tx_monitor", this);
    tx_monitor.vc   = vc;
    tx_monitor.set_context(configuration, status);

    rx_packet_port  = new("rx_packet_port", this);
    rx_monitor      = tnoc_bfm_packet_rx_vc_monitor::type_id::create("rx_monitor", this);
    rx_monitor.vc   = vc;
    rx_monitor.set_context(configuration, status);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    tx_monitor.item_port.connect(tx_packet_port);
    rx_monitor.item_port.connect(rx_packet_port);
  endfunction

  `tue_component_default_constructor(tnoc_bfm_packet_vc_agent)
  `uvm_component_utils(tnoc_bfm_packet_vc_agent)
endclass
`endif
