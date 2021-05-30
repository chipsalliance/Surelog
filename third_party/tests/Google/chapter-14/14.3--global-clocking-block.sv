// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: global_clocking_block
:description: global clocking block test
:tags: 14.3
*/
module top(input clk);

global clocking ck1 @(posedge clk); endclocking

endmodule
