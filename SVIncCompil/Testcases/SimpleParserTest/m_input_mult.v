
module case1 (in1, in2, out2);
input [7:0] in1;
input [2:0] in2;
output out2;
always@(in1 or in2)
 case (in2)
 2'b000 : out2 = in1[0];
 2'b001 : out2 = in1[1];
 2'b010 : out2 = in1[2];
 2'b011 : out2 = in1[3];
 2'b100 : out2 = in1[4];
 2'b101 : out2 = in1[5];
 2'b110 : out2 = in1[6];
 2'b111 : out2 = in1[7];
 endcase

endmodule


module case2 (in1, sel, out2);
input [1:0] in1;
input [2:0] sel;
output [15:0] out2;
reg [7:0] select;
/* address decoder */
always@(sel)
 case (sel)
 3'b000 : select = 8'b00000001;
 3'b001 : select = 8'b00000010;
 3'b010 : select = 8'b00000100;
 3'b011 : select = 8'b00001000;
 3'b100 : select = 8'b00010000;
 3'b101 : select = 8'b00100000;
 3'b110 : select = 8'b01000000;
 3'b111 : select = 8'b10000000;
 endcase
 assign out2[1:0] = in1 & select[0];
 assign out2[3:2] = in1 & select[1];
 assign out2[5:4] = in1 & select[2];
 assign out2[7:6] = in1 & select[3];
 assign out2[9:8] = in1 & select[4];
 assign out2[11:10] = in1 & select[5];
 assign out2[13:12] = in1 & select[6];
 assign out2[15:14] = in1 & select[7];
endmodule


module pri_encooder (Op, Funct, Sel, B);
input [1:0] Op;
input [4:0] Funct;
output [1:0] Sel;
output B;
always@(Op or Funct)
 casex ({Op, Funct})
 {2'b01, 5'bx} : begin
 Sel = 2'b11;
 B = 1'b1;
 end
 {2'b11, 5'b00011} : begin
 Sel = 2'b01;
 B = 1'b1;
 end
 {2'b11, 5'b00001} : begin
 Sel = 2'b10;
 B = 1'b1;
 end
 default : begin
 Sel = 2'bxx;
 B = 1'bx;
 end
 endcase
endmodule
