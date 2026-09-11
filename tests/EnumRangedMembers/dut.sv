// Ranged enum members (LRM 6.19.1): `name[hi:lo] = base` declares the indexed
// constants name<lo>..name<hi>, `base` assigned to the first index and
// incrementing.  Both sized (12'h003) and unsized (3) bounds, plus the
// single-bound `name[N]` form (name0..name(N-1)).
package p;
  typedef enum logic [11:0] {
    csr__minstret                        = 12'hb02,
    csr__mhpmcounter   [12'h003:12'h01f] = 12'hb03,   // mhpmcounter3..31
    csr__mcycleh                         = 12'hb80,
    reg_a              [3:1]             = 12'h010,    // reg_a3,reg_a2,reg_a1
    grp                [4]               = 12'h100     // grp0..grp3
  } csr_addr_e;
endpackage

module dut (output logic [11:0] a, b, c, d);
  import p::*;
  assign a = csr__mhpmcounter3;   // 0xb03
  assign b = csr__mhpmcounter31;  // 0xb1f
  assign c = reg_a1;              // 0x012 (base 0x010 at reg_a3, reg_a2=0x011, reg_a1=0x012)
  assign d = grp0;                // 0x100
endmodule
