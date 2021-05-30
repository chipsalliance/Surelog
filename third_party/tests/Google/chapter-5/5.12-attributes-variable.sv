// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: attributes-variable
:description: Assing attributes to a variable
:tags: 5.12
*/

module top();
  (* fsm_state *)   logic [7:0] a;
  (* fsm_state=1 *) logic [7:0] b;
  (* fsm_state=0 *) logic [7:0] c;
endmodule
