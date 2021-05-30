// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: realtobits_bitstoreal_functions
:description: $realtobits and $bitstoreal test
:tags: 20.5
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: (%f == 12.45)", $bitstoreal($realtobits(12.45)));
end

endmodule
