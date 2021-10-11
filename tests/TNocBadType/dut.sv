interface tnoc_types;
 typedef int tnoc_common_header;
   
endinterface


module top;
   tnoc_types  types;
   
  typedef types.tnoc_common_header  tnoc_common_header;
   
  tnoc_common_header  common_header;
endmodule
