package toto;


function void uvm_default_factory::print ();

  do begin
    wait (m_sync[i].m_state >= UVM_PHASE_SYNCING);
    qs.push_back("  Type Name\n");
     
   end while(m_type_names.next(key));

endfunction

endpackage
