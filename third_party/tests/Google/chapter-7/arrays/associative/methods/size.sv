/*
:name: associative-arrays-size
:description: Test support of associative arrays methods (size)
:tags: 7.9.1 7.9
:type: simulation parsing
*/
module top ();

int arr [ int ];

initial begin
    $display(":assert: (%d == 0)", arr.size);
    arr[ 3 ] = 1;
    $display(":assert: (%d == 1)", arr.size);
    arr[ 16'hffff ] = 2;
    $display(":assert: (%d == 2)", arr.size);
    arr[ 4'b1000 ] = 3;
    $display(":assert: (%d == 3)", arr.size);
end

endmodule
