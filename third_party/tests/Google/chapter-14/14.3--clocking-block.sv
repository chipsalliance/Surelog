// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: clocking_block
:description: clocking block test
:tags: 14.3
*/
module top(input clk);

clocking ck1 @(posedge clk);
	default input #10ns output #5ns;
endclocking

endmodule
