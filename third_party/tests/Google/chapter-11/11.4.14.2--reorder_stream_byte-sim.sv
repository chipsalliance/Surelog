// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: reorder_stream_byte_sim
:description: stream reordering simulation test
:type: simulation parsing
:tags: 11.4.14.2
*/
module top();

int a = {"A", "B", "C", "D"};
int b;

initial begin
	b = {<< byte {a}};
    $display(":assert: (0x44434241 == 0x%x)", b);
end

endmodule
