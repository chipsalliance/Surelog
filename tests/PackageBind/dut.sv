package prim_util_pkg;
   function automatic integer _clog2(integer value);
      integer result;

      for (result = 0; value > 1; result++) begin
	 value = value >> 1;
      end
      return result;
   endfunction
endpackage

module top(output integer o);
   assign o = prim_util_pkg::_clog2(15);
endmodule // top
