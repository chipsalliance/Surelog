`define ASSERT_STATIC_IN_PACKAGE(__name, __prop)              \
  function automatic bit assert_static_in_package_``__name(); \
    bit unused_bit [((__prop) ? 1 : -1)];                     \
    unused_bit = '{default: 1'b0};                            \
    return unused_bit[0];                                     \
  endfunction
`endif  // ASSERT_SV

package pkg_b;
  parameter int ParameterIntEqual4 = 4;
endpackage : pkg_b

package pkg_a;
  parameter int ParameterIntInPkgA = 4;
  `ASSERT_STATIC_IN_PACKAGE(
      ThisNameDoesNotMatter,
      $bits(ParameterIntInPkgA) == $bits(pkg_b::ParameterIntEqual4))
endpackage : pkg_a
