// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: typename_type_function
:description: $typename with type as an argument
:tags: 20.6
:type: simulation parsing
*/

module top();

initial begin
	$display(":assert: ('%s' == 'logic')", $typename(logic));
end

endmodule
