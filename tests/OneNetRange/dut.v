/* verilator lint_off DECLFILENAME */
module dut #(parameter width = 1) (input wire [width-1:0] i, output reg [width-1:0] o);
  ConnectTB #(.width(width)) conntb(.con_i(i),.con_o(o));
  middle #(.width(width)) middle1(conntb);
endmodule


interface ConnectTB #(parameter width = 1) (input wire [width-1:0] con_i, output reg [width-1:0] con_o) ;
endinterface

module middle #(parameter width = 1) (ConnectTB conn);
  SUB #(.width(width)) sub1(.inp(conn.con_i),.out(conn.con_o));
endmodule

module SUB #(parameter width = 1) (input wire [width-1:0] inp, output reg [width-1:0] out);
  assign out = inp;
endmodule

