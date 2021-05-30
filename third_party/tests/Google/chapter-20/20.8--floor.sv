// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: floor_function
:description: $floor test
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%f == 2)", $floor(2.1));
end

endmodule
