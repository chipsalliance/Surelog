
`ifndef ASSERT_SV
`define ASSERT_SV

`define ASSERT_STATIC_IN_PACKAGE(__name, __prop)              \
  function automatic bit assert_static_in_package_``__name(); \
    bit unused_bit [((__prop) ? 1 : -1)];                     \
    unused_bit = '{default: 1'b0};                            \
    return unused_bit[0];                                     \
  endfunction

`endif // ASSERT_SV



package pkg_b;
  parameter int ParameterIntEqual4 = 4;
endpackage : pkg_b


package pkg_a;
  // Comment line 1
  // Comment line 2
  // Comment line 3
  // Comment line 4
  // Comment line 5
  // Comment line 6
  parameter int ParameterIntInPkgA = 4;
  //// The two following lines do not raise any error when uncommented:
  `ASSERT_STATIC_IN_PACKAGE(ThisNameDoesNotMatter, 32 == $bits(pkg_b::ParameterIntEqual4))
  `ASSERT_STATIC_IN_PACKAGE(ThisNameDoesNotMatter, $bits(ParameterIntInPkgA) == 32)
  //// This one does fail:
  `ASSERT_STATIC_IN_PACKAGE(ThisNameDoesNotMatter, $bits(ParameterIntInPkgA) == $bits(pkg_b::ParameterIntEqual4))
endpackage : pkg_a

