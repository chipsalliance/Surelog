// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: string_repl_op
:description: string replication operator test
:tags: 11.4.12.2
:type: simulation parsing
*/
module top();

string str;

initial begin
	str = {4{"test"}};
	$display(":assert:('%s' == 'testtesttesttest')", str);
end

endmodule
