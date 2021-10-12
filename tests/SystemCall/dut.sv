module m2();

let p2(x) = $past(x,,,clock);
assign a = $past(x,,,@(posedge clock));
   
endmodule 
