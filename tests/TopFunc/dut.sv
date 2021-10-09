function automatic int get_1();
   return 1;
endfunction // get_1

module top(output int o);
   assign o = get_1();
endmodule // top
