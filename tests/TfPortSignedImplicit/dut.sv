// A non-ANSI subroutine port with a signing keyword and an implicit type:
// `input signed [7:0] a;` must keep its range and sign; `input signed b;`
// is a signed 1-bit port.
function signed [7:0] incr_sum;
  input signed [7:0] a;
  input signed b;
  logic signed [7:0] tmp;
  begin
    tmp = 'd0;
    for (int i = 0; i < 8; i = i + 1) tmp = tmp + a[i];
    incr_sum = tmp + b;
  end
endfunction
module dut(input logic [7:0] x, input logic b, output logic [7:0] y);
  always_comb y = incr_sum(x, b);
endmodule
