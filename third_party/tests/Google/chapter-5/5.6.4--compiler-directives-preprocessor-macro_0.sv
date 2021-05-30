// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: compiler_directives_preprocessor_macro_0
:description: Read preprocessing macro from template (:defines: marker)
:tags: 5.6.4
:type: preprocessing
:defines: TEST_VAR
*/

`ifdef TEST_VAR
`else
TEST_VAR parsed not correctly from template
`endif
