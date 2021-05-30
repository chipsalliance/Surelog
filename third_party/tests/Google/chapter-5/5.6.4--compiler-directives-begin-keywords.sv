// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: begin-keywords
:description: Begin keywords check
:tags: 5.6.4
*/

`begin_keywords "1364-2001" // use IEEE Std 1364-2001 Verilog keywords
module b_kw();
  reg logic; // OK: "logic" is not a keyword in 1364-2001
endmodule
`end_keywords
