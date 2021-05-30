// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: strobe_task
:description: $strobe test
:tags: 21.2
:type: simulation parsing
*/
module top();

logic clk;
int a;

always @(posedge clk) begin
	$strobe(a);
	$strobeb(a);
	$strobeo(a);
	$strobeh(a);
end

endmodule
