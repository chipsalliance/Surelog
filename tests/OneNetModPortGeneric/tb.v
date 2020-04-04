program TESTBENCH  (interface intf);
  initial begin
    $dumpfile("test.vcd");
    $dumpvars;
    $monitor("@%0dns i = %0d, o = %0d",$time,intf.drive, intf.observe);
    intf.drive = 0;
    #1 assert(intf.drive == intf.observe) $display("OK!"); else $display("intf.drive != intf.observe!");
    #100 intf.drive = 1;
    #1 assert(intf.drive == intf.observe) $display("OK!"); else $display("intf.drive != intf.observe!");
    #100 $finish();
  end
endprogram


module TOP();
  ConnectTB conntb();
  dut dut1( .intf(conntb.dut) );
  TESTBENCH tb(.intf(conntb.tb) );
  OBSERVER obs(.intf(conntb)) ;
endmodule

