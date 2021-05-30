// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: random_weighted_case_randcase_2
:description: randcase test
:tags: 18.16
*/

function int F(int y);
    int a;
    randcase
        y - y : a = 5;
        y + y : a = 10;
    endcase
    return a;
endfunction
