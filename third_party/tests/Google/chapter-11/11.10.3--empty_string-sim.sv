// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: empty_string_sim
:description: empty string simulation test
:type: simulation parsing
:tags: 11.10.3
*/
module top();

bit [8*14:1] a;

initial begin
	a = "";
    $display(":assert: (1 == %d)", a == 0);
end

endmodule
