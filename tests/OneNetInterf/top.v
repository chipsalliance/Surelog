
program TESTBENCH(input wire observe, output reg drive);
  initial begin
    $monitor("@%0dns observe = %0d",$time,observe);
    drive = 0;
    #100 drive = 1;
  end
endprogram

interface ConnectTB (input wire i, output reg o) ;
endinterface

module DUT (ConnectTB conn);
  SUB sub1(.inp(conn.i),.out(conn.o));
endmodule

module SUB (input wire inp, output reg out);
  assign out = inp;
endmodule

module TOP();
  wire i,o;
  ConnectTB conntb(i,o);
  DUT dut(conntb);
  TESTBENCH tb(.observe(conntb.o),.drive(conntb.i));
endmodule
