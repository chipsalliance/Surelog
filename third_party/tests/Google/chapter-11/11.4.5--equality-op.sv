// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: equality_op
:description: equality operator test
:type: simulation parsing
:tags: 11.4.5
*/
module top();

reg [7:0] a, b, c, d, e, f;

initial begin
    a = 8'b1101x001;
    b = 8'b1101x000;
    c = 8'b1101z001;
    d = 8'b1101z000;
    e = 8'b11011001;
    f = 8'b11011000;

    $display(":assert: (0 == %d)", a == b);
    $display(":assert: (0 == %d)", c == d);
    $display(":assert: (0 == %d)", e == f);

    $display(":assert: (0 == %d)", a === b);
    $display(":assert: (0 == %d)", c === d);
    $display(":assert: (0 == %d)", e === f);
end

endmodule
