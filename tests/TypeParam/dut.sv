
module top ();

 mid u1();
 mid #(.TP1(int), .SIZE(20)) u2(); 

endmodule

module mid #(parameter type TP1 = logic, parameter SIZE=10, parameter type TP2 = int);
    TP1 DATA1;
    logic [SIZE:0] a;
    TP2 DATA2;
endmodule
