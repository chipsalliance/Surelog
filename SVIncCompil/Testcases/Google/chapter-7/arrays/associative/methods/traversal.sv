/*
:name: associative-arrays-arg-traversal
:description: Test support of associative arrays methods
:should_fail: 0
:tags: 7.9.8 7.9
*/
module top ();

string map[ int ];
byte ix;
int rc;

initial begin
    map[ 1000 ] = "a";
    rc = map.first( ix );
    $display(":assert: ( (%d == -1) and ('%b' == '11101000') )", rc, ix);
end

endmodule
