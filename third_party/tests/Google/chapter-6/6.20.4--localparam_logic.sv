// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: localparam_logic
:description: localparam with logic type
:tags: 6.20.4
*/
module top();
	localparam [10:0] p = 1 << 5;
	localparam logic [10:0] q = 1 << 5;
endmodule
