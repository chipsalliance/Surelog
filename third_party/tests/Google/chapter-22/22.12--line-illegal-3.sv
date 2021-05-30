// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.12--line-illegal-3
:description: The number parameter shall be a positive integer that specifies the new line number
:should_fail_because: The number parameter shall be a positive integer that specifies the new line number
:tags: 22.12
:type: preprocessing
*/
`line -12 "somefile" 3
