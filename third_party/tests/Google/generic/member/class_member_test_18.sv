// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: class_member_test_18
:description: Test
:tags: 8.3
*/
class myclass;
typedef logic bool;
extern function void subroutine(input bool x);
endclass

function void myclass::subroutine(input bool x); endfunction

module test;
endmodule
