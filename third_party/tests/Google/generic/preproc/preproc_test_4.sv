// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: preproc_test_4
:description: Test
:tags: 5.6.4
:type: preprocessing
*/
`ifdef INSANITY
`define INSANITY // comment
`else
`define SANITY 1
`endif

module test;
endmodule
