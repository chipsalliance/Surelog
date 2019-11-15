////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s        SystemVerilog Tutorial        s////
////s           gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////////////////////////////////////////////////
`ifndef GUARD_RECEIVER
`define GUARD_RECEIVER

class Receiver;

virtual output_interface.OP output_intf;
mailbox rcvr2sb;

//// constructor method ////
function new(virtual output_interface.OP  output_intf_new,mailbox rcvr2sb);
   this.output_intf    = output_intf_new  ;
   if(rcvr2sb == null)
   begin
     $display(" **ERROR**: rcvr2sb is null");
     $finish;
   end
   else
   this.rcvr2sb = rcvr2sb;
endfunction : new  

task start();
logic [7:0] bytes[];
packet pkt;
  forever
  begin
    repeat(2) @(posedge output_intf.clock);
    wait(output_intf.cb.ready)
    output_intf.cb.read <= 1;   
    repeat(2) @(posedge output_intf.clock);
    while (output_intf.cb.ready)
    begin
       bytes = new[bytes.size + 1](bytes);
       bytes[bytes.size - 1] = output_intf.cb.data_out;
       @(posedge output_intf.clock);
    end
    output_intf.cb.read <= 0;   
    @(posedge output_intf.clock);
    $display(" %0d : Receiver : Received a packet of length %0d",$time,bytes.size);
    pkt = new();
    pkt.byte_unpack(bytes);
    pkt.display();
    rcvr2sb.put(pkt); 
    bytes.delete();   
  end
endtask : start

endclass

`endif
