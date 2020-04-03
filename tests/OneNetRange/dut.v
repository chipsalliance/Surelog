interface ConnectTB #(parameter width = 1) (input wire [width-1:0] con_i, output reg [width-1:0] con_o) ;
endinterface

module dut #(parameter width = 1) (ConnectTB conn);
  SUB #(.width(width)) sub1(.inp(conn.con_i),.out(conn.con_o));
endmodule

module SUB #(parameter width = 1) (input wire [width-1:0] inp, output reg [width-1:0] out);
  assign out = inp;
endmodule

