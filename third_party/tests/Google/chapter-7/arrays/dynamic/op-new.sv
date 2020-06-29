/*
:name: dynamic-arrays-op-new
:description: Test dynamic arrays operator new support
:tags: 7.5.1
:type: simulation parsing
*/
module top ();

bit [7:0] arr[];

initial begin
    arr = new [ 4 ];
    arr[ 0 ] = 5;
    arr[ 1 ] = 6;
    arr[ 2 ] = 7;
    arr[ 3 ] = 8;
    $display(":assert: ((%d == 5) and (%d == 6) and (%d == 7) and (%d == 8))",
        arr[ 0 ], arr[ 1 ], arr[ 2 ], arr[ 3 ]);
end

endmodule
