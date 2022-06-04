package pack;

virtual class uvm_event_base;
	protected event      m_event;	

virtual function void do_copy (uvm_object rhs);
uvm_event_base e;

m_event = e.m_event;

endfunction
endclass

endpackage // pack
   
