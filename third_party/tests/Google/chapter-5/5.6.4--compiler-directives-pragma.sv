// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: pragma-directive
:description: Try to set a pragma
:tags: 5.6.4
*/

module ts();
`pragma protect
  wire protected_wire;
`pragma protect end
endmodule
