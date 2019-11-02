

`define dumb \
   begin \
   end


`define uvm_info(ID, MSG, VERBOSITY) \
   begin \
     if (uvm_report_enabled(VERBOSITY,UVM_INFO,ID)) \
       uvm_report_info (ID, MSG, VERBOSITY, uvm_file, uvm_line, "", 1); \
   end


`define wrapper(ID, MSG, VERBOSITY) \
    `uvm_info(ID, MSG, VERBOSITY)

