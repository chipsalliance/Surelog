// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: aborting_productions_break_and_return_0
:description: break statement test
:tags: 18.17.6
*/

function int F();
    int x;
    int break_on = 1;

    randsequence( main )
      main : first second third;
      first : { x = x + 10; };
      second : { if(break_on == 1) break; } fourth;
      third : { x = x + 10; };
      fourth : { x = x + 15; };
    endsequence
    return x;
endfunction
