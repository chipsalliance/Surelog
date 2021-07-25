module top();
   test u1();
   loop u2();
endmodule

module loop();
   loop u1();
endmodule

module test();

   parameter bht_row_width_p = 10;
   if (bht_row_width_p) begin
     test #(.bht_row_width_p(bht_row_width_p-2)) u();
   end
endmodule
