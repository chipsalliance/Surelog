module a(
input interconnect b,
input interconnect [2:0] c,
input interconnect signed g
	);

interconnect net1;
interconnect signed net2;
interconnect unsigned net3;
interconnect signed [1:0] net4;
interconnect signed [1:0][1:0] net5;
interconnect unsigned [1:0][1:0] net6;
interconnect [1:0] net7;
interconnect [1:0][1:0] net8;

interconnect net9 [0:1];
interconnect signed net10 [0:1];
interconnect unsigned net11 [0:1];
interconnect signed [1:0] net12 [0:1];
interconnect signed [1:0][1:0] net13 [0:1];
interconnect unsigned [1:0][1:0] net14 [0:1];
interconnect [1:0] net15 [0:1];
interconnect [1:0][1:0] net16 [0:1];

interconnect net17 [0:1];
interconnect signed net18 [0:1];
interconnect unsigned net19 [0:1];
interconnect signed [1:0] net20 [0:1];
interconnect signed [1:0][1:0] net21 [0:1];
interconnect unsigned [1:0][1:0] net22 [0:1];
interconnect [1:0] net23 [0:1];
interconnect [1:0][1:0] net24 [0:1];

interconnect net17 [0:1][0:1];
interconnect signed net18 [0:1][0:1];
interconnect unsigned net19 [0:1][0:1];
interconnect signed [1:0] net20 [0:1][0:1];
interconnect signed [1:0][1:0] net21 [0:1][0:1];
interconnect unsigned [1:0][1:0] net22 [0:1][0:1];
interconnect [1:0] net23 [0:1][0:1];
interconnect [1:0][1:0] net24 [0:1][0:1];

endmodule


