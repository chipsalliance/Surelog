// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: isunbounded_function
:description: $isunbounded test
:tags: 20.6
:type: simulation parsing
*/

module top();
parameter int i = $;

initial begin
	$display(":assert: (%d == 0)", $isunbounded(1));
	$display(":assert: (%d == 1)", $isunbounded(i));
end

endmodule
