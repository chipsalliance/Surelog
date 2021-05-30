// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: random_production_weights_0
:description: randsequence weights test
:tags: 18.17.1
*/

function int F();
    int x;
    randsequence( main )
        main : first := 1 | second := 0;
        first : { x = -2; };
        second : { x = 2; };
    endsequence
    return x;
endfunction
