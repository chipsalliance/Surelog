module top();


  typedef int triple [1:3];
  triple b = '{1:1, default:0};

  typedef logic [1:0] logic_7_0_t [7:0];

 
   typedef enum logic [1:0] {
    DISABLED, 
    PARALLEL,
    MERGED    
  } unit_type_t;
  
  typedef unit_type_t [0:4] fmt_unit_types_t ;

  typedef unit_type_t [0:4] fmt_unit_types_t_u  [7:8] ;


  typedef fmt_unit_types_t [0:1] opgrp_fmt_unit_types_t  ;

endmodule // top
