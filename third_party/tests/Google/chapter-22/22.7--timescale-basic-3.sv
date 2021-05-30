// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.7--timescale-basic-3
:description: Test
:should_fail_because: The integers in `timescale arguments specify an order of magnitude for the size of the value; the valid integers are 1, 10, and 100
:tags: 22.7
:type: simulation
*/
`timescale 9 ns / 1 ps
