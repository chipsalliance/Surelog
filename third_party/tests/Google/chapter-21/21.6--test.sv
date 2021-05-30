// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: test_plusargs
:description: $test$plusargs test
:tags: 21.6
:type: simulation parsing
*/
module top();

initial begin
	if ($test$plusargs("TEST")) $display("TEST argument found");
	else $display("TEST argument not found");
end

endmodule
