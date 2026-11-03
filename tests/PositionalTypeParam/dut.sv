// A POSITIONAL type-parameter override: `inner #(logic [31:0]) i1 (...)` must
// bind T exactly as the named `inner #(.T(logic [31:0])) i2 (...)` does.
module inner #(parameter type T = logic) (input T d, output T q, output logic [7:0] w);
  assign q = d;
  assign w = $bits(T);
  if ($bits(T) == 32) begin : gen_ok
  end else begin : gen_bad
    $error("type parameter T was not bound to logic [31:0]: $bits(T) = %0d", $bits(T));
  end
endmodule
module dut(input logic [31:0] d, output logic [31:0] q1, output logic [7:0] w1, output logic [31:0] q2, output logic [7:0] w2);
  inner #(logic [31:0]) i1 (.d(d), .q(q1), .w(w1));
  inner #(.T(logic [31:0])) i2 (.d(d), .q(q2), .w(w2));
endmodule
