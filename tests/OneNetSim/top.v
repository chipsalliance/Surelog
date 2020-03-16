
program TESTBENCH(input wire observe, output reg drive);
  initial begin
    $monitor("@%0dns observe = %0d",$time,observe);
    drive = 0;
    #100 drive = 1;
  end
endprogram


module DUT (input wire i, output reg o);
  SUB sub1(.inp(i),.out(o));
endmodule

module SUB (input wire inp, output reg out);
  assign out = inp;
endmodule

module TOP();
  wire i,o;
  DUT dut(i,o);
  TESTBENCH tb(.observe(o),.drive(i));
endmodule
