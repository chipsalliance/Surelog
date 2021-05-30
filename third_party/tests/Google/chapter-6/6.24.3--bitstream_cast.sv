// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: bitstream_cast
:description: bitstream cast function
:tags: 6.24.3
*/
module top();
	struct packed {logic [7:0] a; logic [7:0] b; logic [15:0] c;} s;
	integer a = integer'(s);
endmodule
