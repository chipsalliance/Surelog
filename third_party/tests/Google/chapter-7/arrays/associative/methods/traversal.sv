// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: associative-arrays-arg-traversal
:description: Test support of associative arrays methods
:tags: 7.9.8 7.9
:type: simulation parsing
*/
module top ();

string map[ byte ];
byte ix;
int rc;

initial begin
    map[ 1000 ] = "a";
    rc = map.first( ix );
    $display(":assert: ( ('%0d' == '1') and ('%b' == '11101000') )", rc, ix);
end

endmodule
