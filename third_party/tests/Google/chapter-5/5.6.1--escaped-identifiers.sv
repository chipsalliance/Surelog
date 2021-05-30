// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: escaped-identifiers
:description: Escaped identifiers that should be accepted
:tags: 5.6.1
*/
module identifiers();

  reg \busa+index ;
  reg \-clock ;
  reg \***error-condition*** ;
  reg \net1/\net2 ;
  reg \{a,b} ;
  reg \a*(b+c) ;

endmodule
