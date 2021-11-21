`ifndef TNOC_PACKET_SCOREBOARD_SVH
`define TNOC_PACKET_SCOREBOARD_SVH
class tnoc_packet_scoreboard extends tue_scoreboard #(tnoc_bfm_configuration);
  uvm_analysis_imp_tx #(tnoc_bfm_packet_item, tnoc_packet_scoreboard) tx_packet_export;
  uvm_analysis_imp_rx #(tnoc_bfm_packet_item, tnoc_packet_scoreboard) rx_packet_export;

  tnoc_bfm_packet_item  tx_item_queue[tnoc_bfm_location_id][tnoc_bfm_vc][$];
  uvm_phase             runtime_phase;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tx_packet_export  = new("tx_packet_export", this);
    rx_packet_export  = new("rx_packet_export", this);
  endfunction

  task run_phase(uvm_phase phase);
    runtime_phase = phase;
  endtask

  virtual function void write_tx(tnoc_bfm_packet_item item);
    if (is_acceptable_item(item)) begin
      tnoc_bfm_location_id  source_id = item.source_id;
      tnoc_bfm_vc           vc        = item.vc;
      raise_objection();
      tx_item_queue[source_id][vc].push_back(item);
    end
  endfunction

  virtual function void write_rx(tnoc_bfm_packet_item item);
    tnoc_bfm_location_id  source_id     = item.source_id;
    tnoc_bfm_vc           vc            = item.vc;
    int                   tx_item_index = -1;

    if (is_unexpected_item(source_id, vc)) begin
      `uvm_error(get_name(), $sformatf("unexpected item:\n%s", item.sprint()))
      return;
    end

    foreach (tx_item_queue[source_id][vc][i]) begin
      if (item.compare(tx_item_queue[source_id][vc][i])) begin
        tx_item_index = i;
        break;
      end
    end

    if (tx_item_index >= 0) begin
      `uvm_info(get_name(), $sformatf("rx packet is mathced with tx packet:\n%s", item.sprint()), UVM_MEDIUM)
      tx_item_queue[source_id][vc].delete(tx_item_index);
    end
    else begin
      `uvm_error(get_name(), $sformatf("no tx packet is matched with rx packet:\n%s", item.sprint()))
    end

    drop_objection();
  endfunction

  virtual function bit is_acceptable_item(tnoc_bfm_packet_item item);
    return 1;
  endfunction

  function bit is_unexpected_item(tnoc_bfm_location_id source_id, tnoc_bfm_vc vc);
    if (!tx_item_queue.exists(source_id)) begin
      return 1;
    end
    if (!tx_item_queue[source_id].exists(vc)) begin
      return 1;
    end
    if (tx_item_queue[source_id][vc].size() == 0) begin
      return 1;
    end
    return 0;
  endfunction

  function void raise_objection();
    foreach (tx_item_queue[i, j]) begin
      if (tx_item_queue[i][j].size() > 0) begin
        return;
      end
    end
    runtime_phase.raise_objection(this);
  endfunction

  function void drop_objection();
    foreach (tx_item_queue[i, j]) begin
      if (tx_item_queue[i][j].size() > 0) begin
        return;
      end
    end
    runtime_phase.drop_objection(this);
  endfunction

  `tue_component_default_constructor(tnoc_packet_scoreboard)
  `uvm_component_utils(tnoc_packet_scoreboard)
endclass
`endif
