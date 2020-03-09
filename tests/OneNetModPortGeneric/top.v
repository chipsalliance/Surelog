program TESTBENCH  (interface intf);
  initial begin
    $monitor("@%0dns observe = %0d",$time,intf.observe);
    intf.drive = 0;
    #100 intf.drive = 1;
  end
endprogram

interface ConnectTB;
  logic drive;
  logic observe;
  modport dut (
    input drive,
    output observe
  );
  modport tb (
    output drive,
    input observe
  );
endinterface

  module DUT (interface intf);
  SUB sub1(.inp(intf.drive), .out(intf.observe));
endmodule

module SUB (input wire inp, output reg out);
  assign out = inp;
endmodule

module TOP();
  ConnectTB conntb();
  DUT dut( .intf(conntb.dut) );
  TESTBENCH tb(.intf(conntb.tb) );
endmodule

