`ifndef TNOC_BFM_PACKET_VC_SEQUENCER_SVH
`define TNOC_BFM_PACKET_VC_SEQUENCER_SVH
typedef tue_sequencer #(
  .CONFIGURATION  (tnoc_bfm_configuration ),
  .STATUS         (tnoc_bfm_status        ),
  .REQ            (tnoc_bfm_packet_item   )
) tnoc_bfm_packet_vc_sequencer_base;

class tnoc_bfm_packet_vc_sequencer extends tnoc_bfm_packet_vc_sequencer_base;
  int vc;
  `tue_component_default_constructor(tnoc_bfm_packet_vc_sequencer)
  `uvm_component_utils(tnoc_bfm_packet_vc_sequencer)
endclass
`endif
