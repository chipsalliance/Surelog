program TESTBENCH(input wire observe, output reg drive);
  initial begin
    $monitor("@%0dns observe = %0d",$time,observe);
    drive = 0;
    #100 drive = 1;
  end
endprogram


interface ConnectTB (input wire con_i, output reg con_o) ;
endinterface

module DUT (ConnectTB conn);
  SUB sub1(.inp(conn.con_i),.out(conn.con_o));
endmodule

module SUB (input wire inp, output reg out);
  assign out = inp;
endmodule

module TOP();
  wire i,o;
  ConnectTB conntb(.con_i(i),.con_o(o));
  DUT dut(conntb);
  TESTBENCH tb(.observe(conntb.con_o),.drive(conntb.con_i));
endmodule
