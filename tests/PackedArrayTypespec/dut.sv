module top();

   typedef enum logic [1:0] {
    DISABLED,
    PARALLEL, 
    MERGED    
  } unit_type_t;
  
  typedef unit_type_t [0:4] fmt_unit_types_t;

  typedef fmt_unit_types_t [0:1] opgrp_fmt_unit_types_t;

endmodule

