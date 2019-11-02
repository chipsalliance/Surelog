
program class_t;

  // Class with constructor, with no parameter

  class A;

   function new ();
 
   endfunction


    virtual function void print_tree1(int a);
		
    endfunction

    virtual function int check_tree1();
		
    endfunction

    virtual function int check_tree1();
		
    endfunction

    static function int check_tree2();
    endfunction
 	
    local  function int check_tree2();	
    endfunction
 
 task cfg_dut();
 endtask

 task cfg_dut1();
 endtask

 extern function bit is_recording_enabled();

  extern task burst_read();

  extern task burst_write();
 extern task burst_write();
  extern function bit is_active ();

   extern local static function bit m_predefine_policies();
   extern local static function bit m_predefine_policies();

   extern function new(string name = "uvm_reg_field");

 pure virtual protected function void do_record_field_int();

   constraint legal {
        len >= 2;
        len <= 5;
        payload.size() == len;
   }

endclass

endprogram
