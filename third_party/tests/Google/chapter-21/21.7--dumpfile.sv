// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: vcd_dump_test
:description: vcd dump tests
:tags: 21.7
:type: simulation parsing
*/
module top();

integer i;

initial begin
	$dumpfile("out.vcd");
	$dumpvars;
	$dumplimit(1024*1024);

	i = 1;
	#100 i = 2;
	#200 $dumpoff;
	i = 3;
	#800 $dumpon;
	i = 4;
	#100 $dumpflush;
	i = 5;
	#300 $dumpall;
	i = 6;
end

endmodule
