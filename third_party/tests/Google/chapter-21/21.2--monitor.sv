// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: monitor_task
:description: $monitor test
:tags: 21.2
:type: simulation parsing
*/
module top();

int a;

initial begin
	$monitoron;
	$monitor(a);
	$monitorb(a);
	$monitoro(a);
	$monitorh(a);
	$monitoroff;
end

endmodule
