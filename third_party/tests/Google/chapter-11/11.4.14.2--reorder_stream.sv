// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: reorder_stream
:description: stream reordering test
:tags: 11.4.14.2
*/
module top();

int a = {"A", "B", "C", "D"};
int b;

initial begin
	b = {<< 8 {a}};
end

endmodule
