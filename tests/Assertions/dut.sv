module m(input clock);
logic [15:0] a, b;
logic c, d;
typedef bit [15:0] bits;
// let ones_match(bits x, y) = x == y;
// let same(logic x, y) = x === y;
always_comb
a1:assert((bits'(a) == bits'(b)));
property toggles(bit x, y);
(logic'(x) === logic'(y)) |=> ! (logic'(x) === logic'(y));
endproperty
a2: assert property (@(posedge clock) toggles(c, d));
endmodule : m


module m(input clock);
logic a;
let p1(x) = $past(x);
let p2(x) = $past(x,,,@(posedge clock));
let s(x) = $sampled(x);
always_comb begin
a1: assert(p1(a));
a2: assert(p2(a));
a3: assert(s(a));
end
a4: assert property(@(posedge clock) p1(a));
endmodule : m
