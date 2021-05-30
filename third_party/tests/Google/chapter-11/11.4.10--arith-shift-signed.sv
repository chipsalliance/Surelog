// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: arith_shift_signed
:description: arithmetic shift operator test
:type: simulation parsing
:tags: 11.4.10
*/
module top();

logic signed [7:0] a, b, c;

initial begin
    a = -120; // 128 + 8
    b = (a <<< 3);
    c = (a >>> 3);

    $display(":assert: (  64 == %d)", b);
    $display(":assert: ( -15 == %d)", c);
end

endmodule
