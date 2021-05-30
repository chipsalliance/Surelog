// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: class_member_test_19
:description: Test
:tags: 8.3
*/
class myclass;
typedef logic bool;
localparam int N = 2;
extern function void subr(bool x[N]);
endclass

function void myclass::subr(bool x[N]); endfunction

module test;
endmodule
