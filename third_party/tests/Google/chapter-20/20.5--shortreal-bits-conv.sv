// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: shortrealtobits_bitstoshortreal_functions
:description: $shortrealtobits and $bitstoshortreal test
:tags: 20.5
:type: simulation parsing
*/

module top();

	shortreal s;

initial begin
	s = $bitstoshortreal($shortrealtobits(12.45));
	$display(":assert: (%0d == 1)", (s > 12.449 && s < 12.451));
end

endmodule
