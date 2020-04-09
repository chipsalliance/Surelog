/* verilator lint_off DECLFILENAME */
module dut (input wire i, output reg o);
  assign conntb.drive = i;
  assign o = conntb.observe; 
  ConnectTB conntb();
  middle middle1( .intf(conntb.dut) );
endmodule

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

module middle (interface intf);
  SUB sub1(.inp(intf.drive), .out(intf.observe));
endmodule

module SUB (input wire inp, output reg out);
  assign out = inp;
endmodule

module OBSERVER(interface intf);
   assign obs = intf.observe;
endmodule
