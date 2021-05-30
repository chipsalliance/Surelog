// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: nonescaped-access
:description: Escaped identifiers can be referenced by nonescaped name
:tags: 5.6.1
*/
`default_nettype none
module identifiers();

  reg \cpu3 ;
  wire reference_test;

  assign reference_test = cpu3;

endmodule
