// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: assign_in_exp
:description: assignment in expression test
:tags: 11.3.6
*/
module top();

int a;
int b;

initial begin
        b = (a-=1);
end

endmodule
