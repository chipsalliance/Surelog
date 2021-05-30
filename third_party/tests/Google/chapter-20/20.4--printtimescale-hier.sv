// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: printtimescale_hier_task
:description: $printtimescale hierarchy test
:tags: 20.4
:type: simulation parsing
*/

`timescale 1 ms / 1 us

module top();

initial
	$printtimescale(mod0.m);

endmodule

`timescale 1 us / 1 ns

module mod0();
	mod1 m();
endmodule

`timescale 1 ns / 1 ps

module mod1();
initial
	$display("mod1");
endmodule
