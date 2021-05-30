// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.5.1--define_and_resetall
:description: The text macro facility is not affected by the compiler directive `resetall
:tags: 22.5.1
:type: preprocessing simulation
*/
`define SOMESTRING "somestring"
`resetall

module top ();
initial begin
       	$display(":assert:('%s' == '%s')", `SOMESTRING, "somestring");
end
endmodule
