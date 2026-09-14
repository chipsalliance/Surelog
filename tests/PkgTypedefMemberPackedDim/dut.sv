// A packed-struct member whose element type is a PACKAGE-QUALIFIED typedef of
// a logic / bit vector with an outer packed dimension (`pkg::t [N-1:0] m;`).
// The package-scope typespec branch only wrapped struct / enum / class
// typedefs in a packed_array_typespec, so the outer dimension was dropped and
// the member measured one element wide (OpenTitan dma_pkg::sys_req_t's
// `top_racl_pkg::racl_role_t [SYS_NUM_REQ_CH-1:0] racl_vec`: 183 bits instead
// of 184).  Same-package typedefs already kept their dimension (control).
package ext_pkg;
  parameter int unsigned NrBits = 1;
  typedef logic [NrBits-1:0] role_t;
  typedef logic [1:0]        two_t;
  typedef bit   [3:0]        nib_t;
endpackage
package s_pkg;
  typedef logic [0:0] lrole_t;
  typedef struct packed {
    logic [1:0]              a_plain;    // 2
    lrole_t [1:0]            b_local;    // 2  (control: same-package typedef)
    ext_pkg::role_t [1:0]    c_pkg;      // 2  (was 1)
    ext_pkg::two_t [1:0]     d_pkg2;     // 4  (was 2)
    ext_pkg::nib_t [2:0]     e_pkgbit;   // 12 (was 4)
    logic [1:0][0:0]         f_plain2d;  // 2
  } s_t;
endpackage
module dut (input logic [23:0] d_i, output s_pkg::s_t s_o, output logic [15:0] w_o);
  assign s_o = d_i;
  assign w_o = $bits(s_pkg::s_t);
endmodule
