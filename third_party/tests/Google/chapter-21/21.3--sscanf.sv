// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: sscanf_task
:description: $sscanf test
:tags: 21.3
:type: simulation parsing
*/
module top();

string str = "1234";
int c;

initial begin
	$sscanf(str, "%d", c);
	$display(":assert: (%d == %s)", c, str);
end

endmodule
