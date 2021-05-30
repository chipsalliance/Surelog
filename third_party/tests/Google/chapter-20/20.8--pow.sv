// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: pow_function
:description: $pow test
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%f == 5.0625)", $pow(2.25, 2));
end

endmodule
