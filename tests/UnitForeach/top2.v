

package uvm_pkg; 
 
  function void uvm_sequencer_base::do_print (uvm_printer printer);
    super.do_print(printer);
    printer.print_array_header("arbitration_queue", arb_sequence_q.size());
    foreach (arb_sequence_q[i])
      printer.print_string($sformatf("[%0d]", i),
         $sformatf("%s@seqid%0d",arb_sequence_q[i].request.name(),arb_sequence_q[i].sequence_id), "[");
  endfunction
  

endpackage
