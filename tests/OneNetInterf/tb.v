program TESTBENCH(input wire observe, output reg drive);
  initial begin
    $dumpfile("test.vcd");
    $dumpvars;
    $monitor("@%0dns i = %0d, o = %0d",$time,drive, observe);
    drive = 0;
    #5 drive = 1;
    #100 $finish();
  end
endprogram

module tb();
  wire i,o;
  ConnectTB conntb(.con_i(i),.con_o(o));
  dut dut1(conntb);
  TESTBENCH tb(.observe(conntb.con_o),.drive(conntb.con_i));
endmodule
