// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: associative-arrays-prev
:description: Test support of associative arrays methods (prev)
:tags: 7.9.7 7.9
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

    rc = map.last( s );
    $display(":assert: ((%d == 1) and ('%s' == 'world'))", rc, s);
    rc = map.prev( s );
    $display(":assert: ((%d == 1) and ('%s' == 'sad'))", rc, s);
end

endmodule
