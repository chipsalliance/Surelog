// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: packed-structures-default-members-value
:description: Test packed structures default value support
:should_fail_because: members of packed structures shall not be assigned individual default member values.
:tags: 7.2.2
:type: simulation
*/
module top ();

// Members of unpacked structures containing a union
// as well as members of packed structures shall not be
// assigned individual default member values.

parameter c = 4'h5;

struct packed {
	bit [3:0] lo = c;
	bit [3:0] hi;
} p1;

endmodule
