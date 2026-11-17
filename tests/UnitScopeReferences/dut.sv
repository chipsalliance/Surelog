// IEEE 1800-2023 3.12.1 / 26.5: the compilation-unit ($unit) scope.  A
// typedef, a parameter and a function declared outside every module are
// visible in every module of the unit, by bare name or as $unit::name.
typedef logic [5:0] word_t;
localparam int UNIT_K = 3;
function automatic word_t unit_mix(word_t a);
  return {a[2:0], a[5:3]} ^ word_t'(UNIT_K);
endfunction

module dut(input word_t a, output word_t y, output $unit::word_t z);
  assign y = unit_mix(a);
  assign z = $unit::unit_mix(a + $unit::UNIT_K);
endmodule
