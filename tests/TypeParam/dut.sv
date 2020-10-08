module top ();

 mid u1();
 mid #(.TP1(int)) u2(); 

endmodule

module mid #(parameter type TP1 = logic, parameter type TP2 = int);
    TP1 DATA1;
    TP2 DATA2;
endmodule
