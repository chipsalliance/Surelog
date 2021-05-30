// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: random_function
:description: $random test
:tags: 20.15
:type: simulation parsing
*/

module top();

initial begin
	$display("%d", $random);
end

endmodule
