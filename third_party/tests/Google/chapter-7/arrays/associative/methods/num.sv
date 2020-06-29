/*
:name: associative-arrays-num
:description: Test support of associative arrays methods (num)
:tags: 7.9.1 7.9
:type: simulation parsing
*/
module top ();

int arr [ int ];

initial begin
    $display(":assert: (%d == 0)", arr.num);
    arr[ 3 ] = 1;
    $display(":assert: (%d == 1)", arr.num);
    arr[ 16'hffff ] = 2;
    $display(":assert: (%d == 2)", arr.num);
    arr[ 4'b1000 ] = 3;
    $display(":assert: (%d == 3)", arr.num);
end

endmodule
