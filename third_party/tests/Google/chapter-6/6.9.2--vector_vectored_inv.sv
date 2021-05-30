// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: vector_vectored_inv
:description: vectored vector invalid access tests
:should_fail_because: bit selects are not permitted on vectored vector nets
:tags: 6.9.2
*/
module top();
	logic vectored [15:0] a = 0;

	assign a[1] = 1;
endmodule
