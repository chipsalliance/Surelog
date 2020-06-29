/*
:name: associative-arrays-delete
:description: Test support of associative arrays methods (delete)
:tags: 7.9.2 7.9
:type: simulation parsing
*/
module top ();

int map [ string ];

initial begin
    map[ "hello" ] = 1;
    map[ "sad" ] = 2;
    map[ "world" ] = 3;
    $display(":assert: (%d == 3)", map.size);
    map.delete( "sad" );
    $display(":assert: (%d == 2)", map.size);
    map.delete;
    $display(":assert: (%d == 0)", map.size);
end

endmodule
