// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: urandom_range_0
:description: urandom_range() test
:tags: 18.13.2
*/

class a;
    function int do_urandom_range(int unsigned maxval, int unsigned minval);
        int unsigned val;
        val = $urandom_range(maxval, minval);
        return val;
    endfunction
endclass
