module top();

assert property (up ##[*] up |=> cnt == $past(cnt, 2) + 8'd 2);

assert property (up ##1 up |=> cnt == $past(cnt, 2) + 8'd 2);

assert property (up ##[1:$] up |=> cnt == $past(cnt, 2) + 8'd 2);

assert property (up [*2] |=> cnt == $past(cnt, 2) + 8'd 2);

assert property (up [*n] |=> cnt == $past(cnt, 2) + 8'd 2);

assert property (
		a |=> b throughout (c ##1 d)
);

lock_req: assume property(
            @(posedge clk_i) LockIn |-> lock_d |=> req_tmp == req_q)
              else $fatal (1, "It is disallowed to deassert unserved request signals when LockIn is enabled.");

assume property (
      b |=> ##5 d
);

   
endmodule
