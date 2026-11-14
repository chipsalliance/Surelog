// An automatic function: `t` is automatic (fresh every call), `cnt` is an
// explicitly static local (keeps its value across calls, LRM 6.21).  A local
// with no lifetime keyword takes the lifetime of its subroutine.
module dut(input logic clk, output logic [3:0] q);
  function automatic logic [3:0] next_val();
    logic [3:0] t;           // automatic: a fresh temporary every call
    static logic [3:0] cnt = 4'd3;
    t = cnt + 4'd1;
    cnt = t;
    return cnt;
  endfunction
  always_ff @(posedge clk) q <= next_val();
endmodule
