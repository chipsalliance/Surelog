checker assert_window1 (
  logic test_expr,
  // Expression to be true in the window
  untyped start_event, // Window opens at the completion of the start_event
  untyped end_event,
  // Window closes at the completion of the end_event
  event clock = $inferred_clock,
  logic reset = $inferred_disable,
  string error_msg = "violation",
  coverage_level clevel = cover_all // This argument should be bound to an
  // elaboration time constant expression
);

  default clocking @clock; endclocking
  default disable iff reset;
  bit window = 1'b0, next_window = 1'b1;
  // Compute next value of window
  always_comb begin
    if (reset || window && end_event)
      next_window = 1'b0;
    else if (!window && start_event)
      next_window = 1'b1;
    else
      next_window = window;
    end

  always_ff @clock
    window <= next_window;
  
  property p_window;
    start_event && !window |=> test_expr[+] ##0 end_event;
  endproperty

  a_window: assert property (p_window) else $error(error_msg);

  generate if (clevel != cover_none) begin : cover_b
    cover_window_open: cover property (start_event && !window) $display("window_open covered");

    cover_window: cover property ( 
      start_event && !window
      ##1 (!end_event && window) [*]
      ##1 end_event && window
      ) $display("window covered");
     end : cover_b
   endgenerate
   
endchecker : assert_window1


checker op_test (logic clk, vld_1, vld_2, logic [3:0] opcode);

  bit [3:0] opcode_d1;
  always_ff @(posedge clk) opcode_d1 <= opcode;
  covergroup cg_op;
    cp_op : coverpoint opcode_d1;
  endgroup: cg_op
  cg_op cg_op_1 = new();
  sequence op_accept;
    @(posedge clk) vld_1 ##1 (vld_2, cg_op_1.sample());
  endsequence
  cover property (op_accept);
  
endchecker
