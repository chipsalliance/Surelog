// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: aborting_productions_break_and_return_2
:description: return statement test
:tags: 18.17.6
*/

function int F();
    int x;
    int return_on = 1;
    randsequence( main )
      main : first secondi third;
      first : { x = x + 20; };
      second : { if(return_on == 1) return; x = x + 10; };
      third : { x = x + 5;};
    endsequence
    return x;
endfunction
