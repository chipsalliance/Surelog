// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: value_plusargs
:description: $value$plusargs test
:tags: 21.6
:type: simulation parsing
*/
module top();

integer i;

initial begin
	if ($value$plusargs("TEST=%d", i)) $display("i=%d", i);
	else
		$display("TEST not found");
end

endmodule
