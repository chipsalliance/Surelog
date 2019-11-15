////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s        SystemVerilog Tutorial        s////
////s           gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////////////////////////////////////////////////

class Environment ;


  virtual mem_interface.MEM    mem_intf       ;
  virtual input_interface.IP  input_intf     ;
  virtual output_interface.OP output_intf[4] ;
  
  Driver drvr;
  Receiver rcvr[4];
  Scoreboard sb;
  mailbox drvr2sb ;
  mailbox rcvr2sb ;

function new(virtual mem_interface.MEM    mem_intf_new       ,
             virtual input_interface.IP  input_intf_new     ,
             virtual output_interface.OP output_intf_new[4] );

endfunction : new

function void build();
  
endfunction : build

task reset();
  
endtask : reset
  
task cfg_dut();
  
endtask :cfg_dut

task cfg_dut();
  
endtask :cfg_dut

task start();
  
endtask : start

task wait_for_end();
 
endtask : wait_for_end

task run();
  
endtask : run

task report();
 
endtask:report

endclass

