// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: readmemh_task
:description: $readmemh test
:tags: 21.4
:type: parsing
*/
module top();

logic [31:0] mem1 [1023:0];
string fname1 = "test1.mem";

initial begin
	$readmemh(fname1, mem1);
end

endmodule
