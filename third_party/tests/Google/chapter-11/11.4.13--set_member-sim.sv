// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: set_member_sim
:description: inside operator simulation test
:type: simulation parsing
:tags: 11.4.13
*/
module top();

int a = 12;

initial begin
    $display(":assert: (1 == %d)", a inside {2, 4, 6, 8, 10, 12});
end

endmodule
