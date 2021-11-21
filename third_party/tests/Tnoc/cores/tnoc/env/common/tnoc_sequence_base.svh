`ifndef TNOC_SEQUENCE_BASE_SVH
`define TNOC_SEQUENCE_BASE_SVH
class tnoc_sequence_base #(
  type  SEQUENCER     = uvm_sequencer_base,
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy
) extends tue_sequence #(CONFIGURATION, STATUS);
  function new(string name = "tnoc_sequence_base");
    super.new(name);
    set_automatic_phase_objection(1);
  endfunction

  `uvm_declare_p_sequencer(SEQUENCER)
endclass
`endif
