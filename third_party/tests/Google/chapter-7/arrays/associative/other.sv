// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: associative-arrays-other-types
:description: Test associative arrays support
:tags: 7.8.1
*/
module top ();

typedef struct {
    byte B;
    int I[*];
} Unpkt;

int arr [ Unpkt ];

endmodule
