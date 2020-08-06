/*
:name: associative-arrays-next
:description: Test support of associative arrays methods (next)
:tags: 7.9.6 7.9
:type: simulation parsing
*/
module top ();

int map [ string ];
string s;
int rc;

initial begin
    map[ "hello" ] = 1;
    map[ "sad" ] = 2;
    map[ "world" ] = 3;

    rc = map.first( s );
    $display(":assert: ((%d == 1) and ('%s' == 'hello'))", rc, s);
    rc = map.next( s );
    $display(":assert: ((%d == 1) and ('%s' == 'sad'))", rc, s);
end

endmodule
