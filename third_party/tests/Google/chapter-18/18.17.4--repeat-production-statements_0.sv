// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: repeat_production_statements_0
:description: repeat statement test
:tags: 18.17.4
*/

function int F();
    int x;
    randsequence( main )
      main : first;
      first : repeat(10) second;
      second : { x = x + 1; };
    endsequence
    return x;
endfunction
