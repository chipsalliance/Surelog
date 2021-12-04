module m(logic a, b, c, d, rst1, clk1, clk2);

  logic rst;
  default clocking @(negedge clk1); endclocking
  default disable iff rst1;
  
  property p_triggers(start_event, end_event, form, clk = $inferred_clock,
                      rst = $inferred_disable);
    @clk disable iff (rst) (start_event ##0 end_event[->1]) |=> form;
  endproperty

  property p_multiclock(clkw, clkx = $inferred_clock, clky, w, x, y, z);
    @clkw w ##1 @clkx x |=> @clky y ##1 z;
  endproperty

  a1: assert property (p_triggers(a, b, c));

  a2: assert property (p_triggers(a, b, c, posedge clk1, 1'b0) );

  always @(posedge clk2 or posedge rst) begin
    if (rst)
      #5;
    else begin
      a3: assert property (p_triggers(a, b, c));
    end
  end

  a4: assert property(p_multiclock(negedge clk2, , posedge clk1,a, b, c, d) );
  
endmodule
