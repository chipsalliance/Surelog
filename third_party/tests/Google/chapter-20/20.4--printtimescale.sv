// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: printtimescale_task
:description: $printtimescale test
:tags: 20.4
:type: simulation parsing
*/

`timescale 1 ms / 1 us

module top();

initial
	$printtimescale;

endmodule
