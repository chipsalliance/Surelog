////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s        SystemVerilog Tutorial        s////
////s           gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////////////////////////////////////////////////
`ifndef GUARD_DRIVER
`define GUARD_DRIVER

class Driver;
virtual input_interface.IP  input_intf;
mailbox drvr2sb;
packet gpkt;

//// constructor method ////
function new(virtual input_interface.IP  input_intf_new,mailbox drvr2sb);
  this.input_intf    = input_intf_new  ;
  if(drvr2sb == null)
  begin
    $display(" **ERROR**: drvr2sb is null");
    $finish;
  end
  else
  this.drvr2sb = drvr2sb;
  gpkt = new();
endfunction : new  

/// method to send the packet to DUT ////////
task start();
  packet pkt;
  int length;
  logic [7:0] bytes[];
  repeat(num_of_pkts)
  begin
       repeat(3) @(posedge input_intf.clock);
     pkt = new gpkt;
    //// Randomize the packet /////
    if ( pkt.randomize())
     begin
       $display (" %0d : Driver : Randomization Successesfull.",$time);
       //// display the packet content ///////
       pkt.display();
          
       //// Pack the packet in tp stream of bytes //////
       length = pkt.byte_pack(bytes);
         
       ///// assert the data_status signal and send the packed bytes //////
       foreach(bytes[i])
       begin
          @(posedge input_intf.clock);
          input_intf.cb.data_status <= 1;
          input_intf.cb.data_in <= bytes[i];  
       end 
  
       //// deassert the data_status singal //////
       @(posedge input_intf.clock);
       input_intf.cb.data_status <= 0;
       input_intf.cb.data_in <= 0;  
  
       //// Push the packet in to mailbox for scoreboard /////
       drvr2sb.put(pkt);
       
       $display(" %0d : Driver : Finished Driving the packet with length %0d",$time,length); 
     end
     else
      begin
         $display (" %0d Driver : ** Randomization failed. **",$time);
         ////// Increment the error count in randomization fails ////////
         error++;
      end
  end
endtask : start

endclass

`endif

