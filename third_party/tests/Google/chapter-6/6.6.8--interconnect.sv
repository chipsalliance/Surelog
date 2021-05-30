// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: interconnect
:description: generic interconnect tests
:tags: 6.6.8
*/
module top();
	interconnect bus;

	mod_i m1(bus);
	mod_o m2(bus);
endmodule

module mod_i(input in);

endmodule

module mod_o(output out);

endmodule
