// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: concat_op
:description: concatenation operator test
:tags: 11.4.12
*/
module top();

bit [15:0] a;

bit [7:0] b = 8'b10101100;
bit [7:0] c = 8'b01010011;

initial begin
	a = {b, c};
end

endmodule
