// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: isunknown_function
:description: $isunknown test
:tags: 20.9
:type: simulation parsing
*/

module top();

initial begin
	parameter [3:0] val0 = 4'b000x;
	parameter [3:0] val1 = 4'b000z;
	parameter [3:0] val2 = 4'b00xz;
	parameter [3:0] val3 = 4'b0000;
	$display(":assert: (%d == 1)", $isunknown(val0));
	$display(":assert: (%d == 1)", $isunknown(val1));
	$display(":assert: (%d == 1)", $isunknown(val2));
	$display(":assert: (%d == 0)", $isunknown(val3));
end

endmodule
