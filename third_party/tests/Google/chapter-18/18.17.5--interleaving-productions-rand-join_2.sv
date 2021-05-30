// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: interleaving_productions_rand_join_2
:description: rand join statement test
:tags: 18.17.5
*/

function int F();
    int x;
    randsequence( main )
      main : rand join (0.5) first second;
      first : { x = x + 20; };
      second : { x = x - 10; };
    endsequence
    return x;
endfunction
