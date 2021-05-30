// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.5.1--define_expansion_21
:description: Test
:should_fail_because: text specified for macro text shall not be split across string literals
:tags: 22.5.1
:type: preprocessing
*/
`define first_half "start of string
module top ();
initial $display(`first_half end of string");
endmodule
