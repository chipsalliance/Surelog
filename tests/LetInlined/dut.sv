
module m(/*input clock*/);
logic a;
let p1(x) = $past(x);

let p2(x) = $past(x,,,@(posedge clock));
let s(x) = $sampled(x);

always_comb begin
a1: assert(p1(a));
a2: assert(p2(a));
a3: assert(s(a));
end
//a4: assert property(@(posedge clock) p1(a));

endmodule : m