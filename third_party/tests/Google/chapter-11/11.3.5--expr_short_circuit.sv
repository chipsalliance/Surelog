// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: expr_short_circuit
:description: expression short circuiting test
:type: simulation parsing
:tags: 11.3.5
*/
module top();

logic a = 1;
logic b = 1;
logic c = 0;
logic d;

function int fun(logic a);
    $display(":assert: (False)");
	return a;
endfunction

initial begin
    d = a && (b || fun(c));
    $display(":assert: (1 == %d)", d);
end

endmodule
