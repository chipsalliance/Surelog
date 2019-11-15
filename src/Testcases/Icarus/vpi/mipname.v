module test3;
    initial $mytest;
endmodule

module test2;
    initial $mytest;
    test3 t3();
endmodule

module test;
    initial $mytest;
    test2 t2();
endmodule
