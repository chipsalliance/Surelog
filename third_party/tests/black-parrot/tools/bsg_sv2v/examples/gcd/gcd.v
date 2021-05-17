module gcd #( parameter width_p="inv" )
  (input clk_i
  ,input reset_i
  ,input en_i
  
  ,input                      v_i
  ,input        [width_p-1:0] a_i
  ,input        [width_p-1:0] b_i
  ,output logic               ready_o
  
  ,output logic               v_o
  ,output logic [width_p-1:0] data_o
  ,input                      yumi_i
  );

  typedef enum logic [1:0] {eWAIT, eCALC, eDONE} state_e;

  state_e state_n, state_r;
  logic [width_p-1:0] a_n, a_r;
  logic [width_p-1:0] b_n, b_r;

  wire a_less_than_b = (a_r < b_r);

  wire b_not_equal_zero = (b_r != 0);

  wire [width_p-1:0] a_minus_b = (a_r - b_r);

  always_comb
    begin
      state_n = state_r;
      if ((state_r == eWAIT) & v_i)
        state_n = eCALC;
      else if ((state_r == eCALC) & ~a_less_than_b & !b_not_equal_zero)
        state_n = eDONE;
      else if ((state_r == eDONE) & yumi_i)
        state_n = eWAIT;
    end

  always_ff @(posedge clk_i)
    begin
      if (reset_i) begin
        state_r <= eWAIT;
      end else begin
        state_r <= state_n;
      end
    end

  always_comb
    begin
      if (state_r == eWAIT) begin
        a_n = a_i;
        b_n = b_i;
      end else if ((state_r == eCALC) & a_less_than_b) begin
        a_n = b_r;
        b_n = a_r;
      end else if ((state_r == eCALC) & b_not_equal_zero) begin
        a_n = a_minus_b;
        b_n = b_r;
      end else begin
        a_n = a_r;
        b_n = b_r;
      end
    end

  always_ff @(posedge clk_i)
    begin
      a_r <= a_n;
      b_r <= b_n;
    end

  assign ready_o = state_r == eWAIT;
  assign v_o     = state_r == eDONE;
  assign data_o  = a_r;

endmodule

