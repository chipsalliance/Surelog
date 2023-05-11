package foo_flags;
  typedef struct packed {
    logic a;
  } common_flags_t;
endpackage : foo_flags

/*
package fooes;

  typedef enum logic [1:0] {
    a
  } classes;

endpackage : fooes
*/

package goog;

/*
typedef struct packed {
  logic a;
  fooes::classes b;
} padded_fooes_t;
*/

typedef union packed {
 foo_flags::common_flags_t  [3:0][7:0] atype_t;
 //padded_fooes_t     [3:0][7:0] btype_t;
} top_flag_t;

endpackage: goog

/*
module top ();
  goog::top_flag_t a;
endmodule
*/