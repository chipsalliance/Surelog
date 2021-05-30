// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: arith_shift_assignment_unsigned
:description: arithmetic shift assignment operator test
:type: simulation parsing
:tags: 11.4.10
*/
module top();

logic [7:0] a, b, c;

initial begin
    a = 8;
    b = a;
    c = a;
    b <<<= 3;
    c >>>= 3;

    $display(":assert: (64 == %d)", b);
    $display(":assert: (1 == %d)", c);
end

endmodule
