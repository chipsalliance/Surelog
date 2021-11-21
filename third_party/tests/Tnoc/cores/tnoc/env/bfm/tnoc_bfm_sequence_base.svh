`ifndef TNOC_BFM_SEQUENCE_BASE_SVH
`define TNOC_BFM_SEQUENCE_BASE_SVH
class tnoc_bfm_sequence_base extends tue_sequence #(
  .CONFIGURATION  (tnoc_bfm_configuration ),
  .STATUS         (tnoc_bfm_status        )
);
  `tue_object_default_constructor(tnoc_bfm_sequence_base)
  `uvm_declare_p_sequencer(tnoc_bfm_packet_sequencer)
endclass
`endif
