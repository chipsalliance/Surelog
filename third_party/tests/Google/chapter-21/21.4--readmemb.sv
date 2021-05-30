// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: readmemb_task
:description: $readmemb test
:tags: 21.4
:type: parsing
*/
module top();

logic [31:0] mem0 [1023:0];
string fname0 = "test0.mem";

initial begin
	$readmemb(fname0, mem0);
end

endmodule
