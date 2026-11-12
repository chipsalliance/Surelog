// A generate-for NESTED in another generate scope, bounded by
// `$bits(<type parameter>)`, must iterate over the BOUND type's width
// (common_cells id_queue's exists lookup:
//   for (genvar j = 0; j < $bits(data_t); j++) inside gen_lookup[i]).
// The generate scope's own definition declares no parameters, so the
// bound used to be unevaluable and the loop elaborated ZERO iterations.
// Expected: u.gen_lookup[*].gen_mask[0..5] (override, 6 bits) and
//           v.gen_lookup[*].gen_mask[0..3] (default, 4 bits).
module q #(parameter type data_t = logic [3:0]) (output int o);
  for (genvar i = 0; i < 2; i++) begin : gen_lookup
    for (genvar j = 0; j < $bits(data_t); j++) begin : gen_mask
      localparam int J = j;
    end
  end
  assign o = 0;
endmodule
module dut(output int o, output int p);
  q #(.data_t(logic [5:0])) u (.o);
  q v (.o(p));
endmodule
