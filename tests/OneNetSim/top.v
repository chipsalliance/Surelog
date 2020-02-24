program TESTBENCH(input observe, output drive);
  reg drive;
  wire observe;
  initial begin
    $monitor("@%0dns observe = %0d",$time,observe);
    drive = 0;
    #100 drive = 1;
  end
endprogram

module DUT (input wire i, output reg o);
  assign o = i;
endmodule

module TOP();
  wire i,o;
  DUT dut(i,o);
  TESTBENCH(o,i);
endmodule
