module FullAdder(A,B,Cin,Sum,Cout);
   input [3:0]A,B;
   input Cin;
   output wire [3:0]Sum;
   output wire Cout;
   wire [4:0]temp;
   assign temp=A+B+Cin;
   assign Sum=temp[3:0];
   assign Cout=temp[4];
endmodule


