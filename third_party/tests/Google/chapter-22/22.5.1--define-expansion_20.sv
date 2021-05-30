// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.5.1--define_expansion_20
:description: Test
:tags: 22.5.1
:type: preprocessing
*/
`define var_nand(dly) nand #dly
module top ();
`var_nand(2) g121 (q21, n10, n11);
`var_nand(5) g122 (q22, n10, n11); 
endmodule
