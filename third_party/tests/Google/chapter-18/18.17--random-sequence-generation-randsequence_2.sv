// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: random_sequence_generation_randsequence_2
:description: randsequence test
:tags: 18.17
*/

function int F();
    int x;
    randsequence( main )
        main : first | second;
        first : { x = -2; };
        second : { x = 2; };
    endsequence
    return x;
endfunction
