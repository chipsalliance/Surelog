// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: unary_op_dec_sim
:description: -- operator simulation test
type: simulation parsing
:tags: 11.4.2
*/
module top();

int a = 12;

initial begin
	a--;
    $display(":assert: (11 == %d)", a);
end

endmodule
