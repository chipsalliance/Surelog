`ifndef TNOC_BFM_PACKET_VC_MONITOR_SVH
`define TNOC_BFM_PACKET_VC_MONITOR_SVH

typedef tue_param_monitor #(
  .CONFIGURATION  (tnoc_bfm_configuration ),
  .STATUS         (tnoc_bfm_status        ),
  .ITEM           (tnoc_bfm_packet_item   )
) tnoc_bfm_packet_vc_monitor_base;

class tnoc_bfm_packet_vc_monitor extends tnoc_bfm_component_base #(
  tnoc_bfm_packet_vc_monitor_base
);
  int                   vc;
  tnoc_bfm_flit_vif     vif;
  tnoc_bfm_packet_item  packet_item;
  tnoc_bfm_flit_item    flit_item;
  tnoc_bfm_flit_item    flit_items[$];
  bit                   is_tx_monitor;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    vif = (is_tx_monitor) ? configuration.tx_vif[vc] : configuration.rx_vif[vc];
  endfunction

  task run_phase(uvm_phase phase);
    forever @(vif.monitor_cb) begin
      if (!vif.i_rst_n) begin
        do_reset();
      end
      else begin
        if (vif.monitor_cb.valid && (packet_item == null)) begin
          packet_item = create_item("packet_item");
        end
        if (vif.monitor_cb.valid && (flit_item == null)) begin
          flit_item = sample_flit_item();
        end

        if (!vif.monitor_cb.ack) begin
          continue;
        end

        finish_flit_item();
        if (flit_items[$].is_tail_flit()) begin
          finish_packet_item();
        end
      end
    end
  endtask

  function void do_reset();
    packet_item = null;
    flit_item   = null;
    flit_items.delete();
  endfunction

  function tnoc_bfm_flit_item sample_flit_item();
    tnoc_bfm_flit       flit;
    tnoc_bfm_flit_item  flit_item;
    flit      = vif.monitor_cb.flit;
    flit_item = tnoc_bfm_flit_item::create_flit_item("flit_item", flit);
    void'(begin_child_tr(flit_item, packet_item.tr_handle));
    return flit_item;
  endfunction

  function void finish_flit_item();
    flit_items.push_back(flit_item);
    end_tr(flit_item);
    flit_item = null;
  endfunction

  function void finish_packet_item();
    packet_item.unpack_flit_items(flit_items);
    write_item(packet_item);
    flit_items.delete();
    packet_item = null;
  endfunction

  `tue_component_default_constructor(tnoc_bfm_packet_vc_monitor)
endclass

class tnoc_bfm_packet_tx_vc_monitor extends tnoc_bfm_packet_vc_monitor;
  function new(string name = "tnoc_bfm_packet_tx_vc_monitor", uvm_component parent = null);
    super.new(name, parent);
    is_tx_monitor = 1;
  endfunction
  `uvm_component_utils(tnoc_bfm_packet_tx_vc_monitor)
endclass

class tnoc_bfm_packet_rx_vc_monitor extends tnoc_bfm_packet_vc_monitor;
  function new(string name = "tnoc_bfm_packet_rx_vc_monitor", uvm_component parent = null);
    super.new(name, parent);
    is_tx_monitor = 0;
  endfunction
  `uvm_component_utils(tnoc_bfm_packet_rx_vc_monitor)
endclass
`endif
