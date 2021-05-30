// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: associative-arrays-as-arguments
:description: Test passing associative array as arugments support
:tags: 7.9.10 7.8
:type: simulation parsing
*/
module top ();

string arraya[int];

task fun (string arrayb[int]);
	arrayb[ 1 ] = "d";
	$display(":assert: (('%s' == 'a') and ('%s' == 'd') and ('%s' == 'c'))",
		arrayb[0], arrayb[1], arrayb[2]);
endtask

initial begin
	arraya[ 0 ] = "a";
	arraya[ 1 ] = "b";
	arraya[ 2 ] = "c";

	$display(":assert: (('%s' == 'a') and ('%s' == 'b') and ('%s' == 'c'))",
		arraya[0], arraya[1], arraya[2]);

	fun(arraya);

	$display(":assert: (('%s' == 'a') and ('%s' == 'b') and ('%s' == 'c'))",
		arraya[0], arraya[1], arraya[2]);
end

endmodule
