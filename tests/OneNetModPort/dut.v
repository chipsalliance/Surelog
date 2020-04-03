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

module dut (ConnectTB.dut intf);
  SUB sub1(.inp(intf.drive), .out(intf.observe));
endmodule

module SUB (input wire inp, output reg out);
  assign out = inp;
endmodule
