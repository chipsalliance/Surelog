package foo_flags_pkg; 
  typedef struct packed {
    logic a;
  } common_flags_t;

endpackage : foo_flags_pkg


typedef union packed {
    foo_flags_pkg::common_flags_t  [3:0][7:0] atype_t;
} top_flag_t;
