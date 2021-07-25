package prim_util_pkg;
   function automatic int get_5();
      int result = 5;
      return result;
   endfunction // get_5
endpackage // prim_utilt_pkg

package lc_ctrl_state_pkg;
   import prim_util_pkg::get_5;
endpackage // lc_ctrl_state_pkg

module top(output int o);
   assign o = lc_ctrl_state_pkg::get_5();
endmodule; // top
