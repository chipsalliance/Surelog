// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: cond_op
:description: ?: operator test
:tags: 11.4.11
*/
module top();

int a = 12;
int b = 5;
int c;

initial begin
	c = (a > b) ? 11 : 13;
end

endmodule
