/*
:name: associative-arrays-last
:description: Test support of associative arrays methods (last)
:should_fail: 0
:tags: 7.9.5 7.9
*/
module top ();

int map [ string ];
string s;
int rc;

initial begin
    // empty, should return zero
    rc = map.last( s );
    $display(":assert: (%d == 0)", rc);

    map[ "hello" ] = 1;
    map[ "sad" ] = 2;
    map[ "world" ] = 3;
    rc = map.last( s );
    $display(":assert: ((%d == 1) and ('%s' == 'world'))", rc, s);
end

endmodule
