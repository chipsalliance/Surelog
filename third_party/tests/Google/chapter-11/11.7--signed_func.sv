// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: signed_func
:description: $signed() test
:tags: 11.7
*/
module top();

logic signed [7:0] a;

initial begin
	a = $signed(4'b1000);
end

endmodule
