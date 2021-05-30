// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: set_member
:description: inside operator test
:tags: 11.4.13
*/
module top();

int a;
int b = 12;
localparam c = 5;
localparam d = 7;

initial begin
	a = b inside {c, d};
end

endmodule
