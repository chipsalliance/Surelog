module gates();

wire out0;
wire out1;
wire out2;
reg  in1,in2,in3,in4;

not U1(out0,in1);
and U2(out1,in1,in2,in3,in4);
xor U3(out2,in1,in2,in3);

initial begin
  $monitor(
  "in1=%b in2=%b in3=%b in4=%b out0=%b out1=%b out2=%b",
   in1,in2,in3,in4,out0,out1,out2); 
  in1 = 0;
  in2 = 0;
  in3 = 0;
  in4 = 0;
  #1 in1 = 1;
  #1 in2 = 1;
  #1 in3 = 1;
  #1 in4 = 1;
  #1 $finish; 
end	

endmodule // gates

module transmission_gates();  

reg data_enable_low, in;
wire data_bus, out1, out2;

bufif0 U1(data_bus,in, data_enable_low);
buf  U2(out1,in);
not U3(out2,in);

initial begin
  $monitor(
    "@%g in=%b data_enable_low=%b out1=%b out2= b data_bus=%b", 
    $time, in, data_enable_low, out1, out2, data_bus);
  data_enable_low = 0;
  in = 0;
  #4 data_enable_low = 1;
  #8 $finish;
end

always #2 in = ~in;

endmodule // transmission_gates

module switch_primitives();

wire  net1, net2, net3;
wire  net4, net5, net6;

tranif0 my_gate1 (net1, net2, net3);
rtranif1 my_gate2 (net4, net5, net6);

endmodule // switch_primitives

module dff_from_nand();
wire Q,Q_BAR;
reg D,CLK;

nand U1 (X,D,CLK) ;
nand U2 (Y,X,CLK) ;
nand U3 (Q,Q_BAR,X);
nand U4 (Q_BAR,Q,Y);

// Testbench of above code
initial begin
  $monitor("CLK = %b D = %b Q = %b Q_BAR = %b",CLK, D, Q, Q_BAR);
  CLK = 0;
  D = 0;
  #3 D = 1;
  #3 D = 0;
  #3 $finish;
end	

always #2 CLK = ~CLK;

endmodule // dff_from_nand

module mux_from_gates ();
reg c0,c1,c2,c3,A,B; 
wire Y; 
//Invert the sel signals 
not (a_inv, A); 
not (b_inv, B); 
// 3-input AND gate 
and (y0,c0,a_inv,b_inv); 
and (y1,c1,a_inv,B); 
and (y2,c2,A,b_inv); 
and (y3,c3,A,B); 
// 4-input OR gate 
or (Y, y0,y1,y2,y3); 

// Testbench Code goes here
initial begin
  $monitor (
   "c0 = %b c1 = %b c2 = %b c3 = %b A = %b B = %b Y = %b",
   c0, c1, c2, c3, A, B, Y);
  c0 = 0;
  c1 = 0;
  c2 = 0;
  c3 = 0;
  A = 0;
  B = 0;
  #1 A  = 1;
  #2 B  = 1;
  #4 A  = 0;
  #8 $finish;
end

always #1 c0 = ~c0;
always #2 c1 = ~c1;
always #3 c2 = ~c2;
always #4 c3 = ~c3;
   
endmodule // mux_from_gates

// Structural model of AND gate from two NANDS 
module and_from_nand();

reg X, Y;
wire F, W;
// Two instantiations of the module NAND
nand U1(W,X, Y);
nand U2(F, W, W);

// Testbench Code
initial begin
  $monitor ("X = %b Y = %b F = %b", X, Y, F);
  X = 0;
  Y = 0;
  #1 X = 1;
  #1 Y = 1;
  #1 X = 0; 
  #1 $finish;
end

endmodule // and_from_nand

module delay_example();

wire out1,out2,out3,out4,out5,out6;
reg b,c;

// Delay for all transitions
or     #5                   u_or     (out1,b,c);
// Rise and fall delay
and    #(1,2)               u_and    (out2,b,c);
// Rise, fall and turn off delay
bufif1    #(1,2,3)             u_nor    (out3,b,c);
//One Delay, min, typ and max
nand   #(1:2:3)             u_nand   (out4,b,c);
//Two delays, min,typ and max
buf    #(1:4:8,4:5:6)       u_buf    (out5,b);
//Three delays, min, typ, and max
notif1 #(1:2:3,4:5:6,7:8:9) u_notif1 (out6,b,c);

//Testbench code
initial begin
  $monitor (
  "Time=%g b=%b c=%b  out1=%b out2=%b out3=%b out4=%b out5=%b out6=%b", 
    $time, b, c , out1, out2, out3, out4, out5, out6); 
  b = 0;
  c = 0;
  #10 b = 1;
  #10 c = 1;
  #10 b = 0;
  #10 $finish;
end	

endmodule // delay_example

module n_in_primitive();

wire out1,out2,out3;
reg in1,in2,in3,in4;

// Two input AND gate
and u_and1 (out1, in1, in2);
// four input AND gate 
and u_and2 (out2, in1, in2, in3, in4);
// three input XNOR gate 
xnor u_xnor1 (out3, in1, in2, in3);

//Testbench Code
initial begin
  $monitor (
  "in1 = %b in2 = %b in3 = %b in4 = %b out1 = %b out2 = %b out3 = %b",
  in1, in2, in3, in4, out1, out2, out3);
  in1 = 0;
  in2 = 0;
  in3 = 0;
  in4 = 0;
  #1 in1 = 1;
  #1 in2 = 1;
  #1 in3 = 1;
  #1 in4 = 1;
  #1 $finish;
end

endmodule // n_in_primitive

module n_out_primitive();

wire out,out_0,out_1,out_2,out_3,out_a,out_b,out_c;
wire in;

// one output Buffer gate
buf u_buf0 (out,in);
// four output Buffer gate 
buf u_buf1 (out_0, out_1, out_2, out_3, in);
// three output Invertor gate 
not u_not0 (out_a, out_b, out_c, in);
 
endmodule // n_out_primitive

module half_adder(Sum, Carry, A, B) ;
 input A, B ;
 output wire Sum, Carry ;
 xor #2 U1 (Sum, A, B) ;
 and #1 U2 (Carry, A, B) ;
endmodule // half_adder


module gate_array();
   
wire [7:0] out, in1, in2 ;
nand n_gate [7:0] (out, in1, in2) ;

endmodule
   
