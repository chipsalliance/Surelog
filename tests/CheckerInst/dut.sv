module top;
  logic a, b, c, clk;
  global clocking top_clocking @(clk); endclocking

  property p1(req, ack);
    @($global_clock) req |=> ack;
  endproperty

  property p2(req, ack, interrupt);
    @($global_clock) accept_on(interrupt) p1(req, ack);
  endproperty

  my_checker check( 
	  p2(a, b, c), 
	  @($global_clock) a[*1:$] ##1 b);
endmodule

checker my_checker(property p, sequence s);
  logic checker_clk;
  global clocking checker_clocking @(checker_clk); endclocking
  assert property (p);
  cover property (s);
endchecker

