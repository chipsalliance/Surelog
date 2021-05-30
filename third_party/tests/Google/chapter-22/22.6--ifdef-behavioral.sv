// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.6--ifdef-behavioral
:description: Test
:tags: 22.6
:type: preprocessing
*/
module and_op (a, b, c);
	output a;
	input b, c;
	`ifdef behavioral
		wire a = b & c;
	`else
		and a1 (a,b,c);
	`endif
endmodule
