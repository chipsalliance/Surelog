module test();
wire [1:0] a;
wire [9:0] b;
wire [0:9] d;
a       a1(.a(c));
b       b1(.a(a[0]));
c       ci(.a({a, b}));
d       d1(.a({d[0:9], a[1:0]}), .d(c));
f       f(a);
a       a3(a[1]);
a       a4({a[1]});
g       g({a,b});
e       e();

initial 
  $display("PASSED");
endmodule


module a(a);
input a;
endmodule



module b(.a(b));
input b;
endmodule


module c(.a({b, c}) );
input  b;
input c;
endmodule



module d(.a({b, c}), d);
input [10:0] b;
input c, d;
endmodule

module e();
endmodule

module f({a, b});
input a, b;
endmodule
module g(a);
input [11:0] a;
endmodule




/*

module InoutConnect(
                    .X1(internal), 
                    .X2(internal)
                    );


   inout internal;
endmodule 

*/