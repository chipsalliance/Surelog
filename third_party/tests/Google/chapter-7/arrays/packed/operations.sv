// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: operations-on-packed-arrays-rw
:description: Test packed arrays operations support (R & W)
:tags: 7.4.3
:type: simulation parsing
*/
module top ();

bit [7:0] arr;

initial begin
	arr = 8'h00;
	$display(":assert: ('%h' == '00')", arr);

	arr = 8'hde;
	$display(":assert: ('%h' == 'de')", arr);

	arr = 8'had;
	$display(":assert: ('%h' == 'ad')", arr);
end

endmodule
