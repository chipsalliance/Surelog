// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: debug-directives
:description: Debugging compiler directives
:tags: 5.6.4
*/

module directives();
  initial $display("At %s @ %d\n", `__FILE__, `__LINE__);
endmodule;
