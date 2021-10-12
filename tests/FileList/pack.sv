package prim_util_pkg;

 function automatic integer vbits(integer value);
    return (value == 1) ? 1 : $clog2(value);
  endfunction

endpackage // prim_util_pkg
   
