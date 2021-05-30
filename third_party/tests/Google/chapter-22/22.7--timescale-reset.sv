// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.7--timescale-reset
:description: Test
:tags: 22.7
:type: preprocessing
*/
`timescale 1 ns / 1 ps
`resetall
`timescale 10 us / 100 ns
