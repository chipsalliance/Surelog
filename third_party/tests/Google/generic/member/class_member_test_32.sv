// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: class_member_test_32
:description: Test
:tags: 8.3
*/
class myclass;
int dout;
int n_bits;

function void shifter;
  for (var int shft_idx=1, bit c=1'b0; shft_idx < n_bits;
       shft_idx++) begin
    dout = {dout} << 1;
  end
endfunction
endclass

module test;
endmodule
