package toto;

   function automatic bit uvm_string_to_action (string action_str, output uvm_action action);
      string actions[$];
    endfunction
    
    function uvm_object uvm_object::clone();
     
      tmp = this.create(get_name());
      
      tmp.copy(this);
 
    endfunction
    

function this_type m_initialize();
   if(m_b_inst == null) begin
     m_b_inst = new;
     m_pool = new (2);
   end
   return m_b_inst;
 endfunction


function void uvm_reg::add_field(uvm_reg_field field);
   
   if (this.fields[idx-1].get_lsb_pos_in_register()) begin
   end
   
endfunction

function bit uvm_transaction::is_recording_enabled ();
  return (this.stream_handle != null);
endfunction // is_recording_enabled
   
function void uvm_reg_backdoor::start_update_thread(uvm_object element);
      uvm_reg rg;
      if (this.m_update_thread.exists(element)) begin
         this.kill_update_thread(element);
      end
    
   endfunction
   
endpackage
