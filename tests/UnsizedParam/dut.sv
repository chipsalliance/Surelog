module submodule();
   parameter int X = 20;
   typedef logic [X-1:0] my_type_t;
   parameter my_type_t Y = '1;
   assign a = int'(Y);
endmodule

module top();
   submodule u_sub_default();
   submodule #(.X(5)) u_sub_5();
endmodule
