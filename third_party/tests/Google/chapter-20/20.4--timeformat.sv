// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: timeformat_task
:description: $timeformat test
:tags: 20.4
:type: simulation parsing
*/

`timescale 1 fs / 1 fs

module top();

initial begin
	$timeformat(-9, 5, "ns", 10);
	$display("%t", $realtime);
end

endmodule
