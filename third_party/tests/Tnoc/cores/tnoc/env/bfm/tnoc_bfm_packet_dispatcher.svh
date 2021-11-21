`ifndef TNOC_BFM_PACKET_DISPATCHER_SVH
`define TNOC_BFM_PACKET_DISPATCHER_SVH
typedef tue_sequence_item_dispatcher #(
  .CONFIGURATION  (tnoc_bfm_configuration ),
  .STATUS         (tnoc_bfm_status        ),
  .ITEM           (tnoc_bfm_packet_item   )
) tnoc_bfm_packet_dispatcher_base;

class tnoc_bfm_packet_dispatcher extends tnoc_bfm_packet_dispatcher_base;
  local tnoc_bfm_packet_vc_sequencer  vc_sequencer[int];

  function void set_vc_sequencer(int vc, tnoc_bfm_packet_vc_sequencer vc_sequencer);
    this.vc_sequencer[vc] = vc_sequencer;
  endfunction

  protected function uvm_sequencer_base select_sequencer(
    tnoc_bfm_packet_item  item
  );
    return vc_sequencer[item.vc];
  endfunction

  `tue_object_default_constructor(tnoc_bfm_packet_dispatcher)
endclass
`endif
