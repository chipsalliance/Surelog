
program TESTBENCH #(parameter width = 1) (input wire [width-1:0] observe, output reg [width-1:0] drive);
  initial begin
    $monitor("@%0dns observe = %0d",$time,observe);
    drive = 000;
    #100 drive = 111;
  end
endprogram


interface ConnectTB #(parameter width = 1) (input wire [width-1:0] con_i, output reg [width-1:0] con_o) ;
endinterface

module DUT #(parameter width = 1) (ConnectTB conn);
  SUB #(.width(width)) sub1(.inp(conn.con_i),.out(conn.con_o));
endmodule

module SUB #(parameter width = 1) (input wire [width-1:0] inp, output reg [width-1:0] out);
  assign out = inp;
endmodule

module TOP();
  parameter width = 16;
  wire [width-1:0] i;
  wire [width-1:0] o;
  ConnectTB #(width) conntb(.con_i(i),.con_o(o));
  DUT #(width) dut(conntb);
  TESTBENCH #(width) tb(.observe(conntb.con_o),.drive(conntb.con_i));
endmodule
