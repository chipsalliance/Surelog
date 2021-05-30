// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.9--unconnected_drive-invalid-3
:description: Test
:should_fail_because: use a strength keyword with `nounconnected_drive macro
:tags: 22.9
:type: simulation
*/
`unconnected_drive pull0 
`nounconnected_drive pull0
