// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: urandom_0
:description: urandom() test
:tags: 18.13.1
*/

class a;
    function int unsigned do_urandom();
        int unsigned x;
        x = $urandom();
        return x;
    endfunction
endclass
