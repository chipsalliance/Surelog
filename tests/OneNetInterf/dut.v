

interface ConnectTB (input wire con_i, output reg con_o) ;
endinterface

module dut (ConnectTB conn);
  SUB sub1(.inp(conn.con_i),.out(conn.con_o));
endmodule

module SUB (input wire inp, output reg out);
  assign out = inp;
endmodule
