// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: array_addressing
:description: array addressing test
:tags: 11.5.2
*/
module top();
logic [7:0] mem [0:1023];
logic [7:0] a;

initial begin
	a = mem[123];
end

endmodule
