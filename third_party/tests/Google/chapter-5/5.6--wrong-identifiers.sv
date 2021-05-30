// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: wrong-identifiers
:description: Identifiers that should not be accepted
:should_fail_because: The first character of a simple identifier shall not be a digit or $
:tags: 5.6
*/
module identifiers();
  reg $dollar;
  reg 0number;
endmodule
