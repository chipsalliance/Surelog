// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: define-directive
:description: Define and undef checks
:tags: 5.6.4
*/

`define XXX 1

`ifdef XXX
`undef XXX
`elsif YYY 
`define XXX 0
`endif

`ifndef YYY
`define YYY 0
`else
`define XXX 0
`endif

`undefineall

module d();
endmodule
