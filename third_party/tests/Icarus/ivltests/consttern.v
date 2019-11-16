module rega(A);
input A;
endmodule

module test(A);
input A;

    rega a (.A(A[(5 > 4 ? 0 : 1) : 0]));
    rega b (.A(A[(4 < 5 ? 0 : 1) : 0]));

    initial $display("PASSED");
endmodule
