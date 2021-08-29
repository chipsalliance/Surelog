module top(output int o);
   assign o = get_a1();

   function automatic int get_a1();
      int a [2] = '{0, 1};
      return a[1];
   endfunction // get_a1
endmodule // top
