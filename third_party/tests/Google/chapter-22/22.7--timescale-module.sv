// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.7--timescale-module
:description: Test
:tags: 22.7
:type: preprocessing
*/
`timescale 10 ns / 1 ns
module test;
	logic set;
	parameter d = 1.55;
	initial begin
		#d set = 0;
		#d set = 1;
	end
endmodule
