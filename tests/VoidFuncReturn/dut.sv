module top();

function void add(int a, int b);
$display("%d+%d=", a, b);
return a + b;
endfunction

initial
$display("%d", add(45, 90));

endmodule
