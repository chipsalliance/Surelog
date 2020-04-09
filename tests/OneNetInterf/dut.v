/* verilator lint_off DECLFILENAME */
module dut (input wire i, output reg o);
  ConnectTB conntb(.con_i(i),.con_o(o));
  middle middle1(conntb);
endmodule

interface ConnectTB (input wire con_i, output reg con_o) ;
endinterface

module middle (ConnectTB conn);
  SUB sub1(.inp(conn.con_i),.out(conn.con_o));
endmodule

module SUB (input wire inp, output reg out);
  assign out = inp;
endmodule
