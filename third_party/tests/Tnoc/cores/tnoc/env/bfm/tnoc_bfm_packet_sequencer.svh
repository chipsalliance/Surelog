`ifndef TNOC_BFM_PACKET_SEQUENCER_SVH
`define TNOC_BFM_PACKET_SEQUENCER_SVH
typedef tue_sequencer #(
  .CONFIGURATION  (tnoc_bfm_configuration ),
  .STATUS         (tnoc_bfm_status        ),
  .REQ            (tnoc_bfm_packet_item   )
) tnoc_bfm_packet_sequencer_base;

class tnoc_bfm_packet_sequencer extends tnoc_bfm_packet_sequencer_base;
  uvm_analysis_imp #(
    tnoc_bfm_packet_item, tnoc_bfm_packet_sequencer
  ) rx_packet_export;

        tnoc_bfm_packet_vc_sequencer  vc_sequencers[int];
  local tnoc_bfm_packet_dispatcher    packet_dispather;
  local uvm_event                     packet_waiters[$];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    rx_packet_export  = new("rx_packet_export", this);
    packet_dispather  = new("packet_dispather");
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
      tnoc_bfm_packet_item  item;
      get_next_item(item);
      packet_dispather.dispatch(item);
      item_done();
    end
  endtask

  function void write(tnoc_bfm_packet_item packet_item);
    foreach (packet_waiters[i]) begin
      packet_waiters[i].trigger(packet_item);
    end
    packet_waiters.delete();
  endfunction

  function void connect_vc_agent(tnoc_bfm_packet_vc_agent vc_agent);
    vc_sequencers[vc_agent.vc]  = vc_agent.sequencer;
    vc_agent.rx_packet_port.connect(rx_packet_export);
    packet_dispather.set_vc_sequencer(vc_agent.vc, vc_agent.sequencer);
  endfunction

  task get_rx_packet(ref tnoc_bfm_packet_item packet_item);
    uvm_event waiter  = get_packet_waiter();
    waiter.wait_ptrigger();
    $cast(packet_item, waiter.get_trigger_data());
  endtask

  task get_rx_request_packet(ref tnoc_bfm_packet_item packet_item);
    while (1) begin
      tnoc_bfm_packet_item  item;
      get_rx_packet(item);
      if (item.is_request()) begin
        packet_item = item;
        return;
      end
    end
  endtask

  task get_rx_response_packet(ref tnoc_bfm_packet_item packet_item);
    while (1) begin
      tnoc_bfm_packet_item  item;
      get_rx_packet(item);
      if (item.is_response()) begin
        packet_item = item;
        return;
      end
    end
  endtask

  local function uvm_event get_packet_waiter();
    uvm_event waiter  = new();
    packet_waiters.push_back(waiter);
    return waiter;
  endfunction

  `tue_component_default_constructor(tnoc_bfm_packet_sequencer)
  `uvm_component_utils(tnoc_bfm_packet_sequencer)
endclass
`endif
