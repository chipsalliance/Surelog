package foo_flags;
  typedef struct packed {
    logic a;
  } common_flags_t;
endpackage : foo_flags


package fooes;

  typedef enum logic [1:0]{
    a
  } classes;

endpackage : fooes

typedef struct packed {
  fooes::classes b;
} padded_fooes_t;

typedef union packed {
  foo_flags::common_flags_t  atype_t;
  padded_fooes_t      btype_t;
} top_flag_t;

module top(input top_flag_t a , output top_flag_t b);
  assign b = a;
endmodule