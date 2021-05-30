// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: write_boh
:description: $write test
:tags: 21.2
:type: simulation parsing
*/
module top();

initial begin
	int val = 1234;
	$writeb(val);
	$writeo(val);
	$writeh(val);
end

endmodule
