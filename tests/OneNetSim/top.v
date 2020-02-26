
program TESTBENCH(input wire observe, output reg drive);
  initial begin
    $monitor("@%0dns observe = %0d",$time,observe);
    drive = 0;
    #100 drive = 1;
  end
endprogram

module DUT (input wire i, output reg o);
  SUB sub1(i,o);
endmodule

module SUB (input wire i, output reg o);
  assign o = i;
endmodule

module TOP();
  wire i,o;
  DUT dut(i,o);
  TESTBENCH tb(o,i);
endmodule
