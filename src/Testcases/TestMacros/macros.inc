


`define uvm_file `__FILE__


`define uvm_line `__LINE__


`define uvm_info(ID, MSG, VERBOSITY) \
   begin \
     if (uvm_report_enabled(VERBOSITY,UVM_INFO,ID)) \
       uvm_report_info (ID, MSG, VERBOSITY, `uvm_file, `uvm_line, "", 1); \
   end

