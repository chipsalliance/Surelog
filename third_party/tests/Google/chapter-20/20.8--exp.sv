// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: exp_function
:description: $exp test
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%f > 2.718) and (%f < 2.719)", $exp(1), $exp(1));
end

endmodule
