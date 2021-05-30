// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: log10_function
:description: $log10 test
:tags: 20.8
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%d == 2)", $log10(100));
end

endmodule
