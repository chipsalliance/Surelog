// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: desc_test_17
:description: Test
:type: preprocessing
:tags: 5.6.4
*/
`ifdef ASIC_OR_FPGA
module module_asic;
endmodule
module module_fpga;
endmodule
`else
`endif
