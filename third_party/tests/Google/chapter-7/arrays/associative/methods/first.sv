/*
:name: associative-arrays-first
:description: Test support of associative arrays methods (first)
:tags: 7.9.4 7.9
:type: simulation parsing
*/
module top ();

int map [ string ];
string s;
int rc;

initial begin
    // empty, should return zero
    rc = map.first( s );
    $display(":assert: (%d == 0)", rc);

    map[ "hello" ] = 1;
    map[ "sad" ] = 2;
    map[ "world" ] = 3;
    rc = map.first( s );
    $display(":assert: ((%d == 1) and ('%s' == 'hello'))", rc, s);
end

endmodule
