// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: unpack_stream_inv
:description: invalid stream unpack test
:should_fail_because: stream is wider than assignment target
:tags: 11.4.14.3
:type: simulation
*/
module top();

int a = 1;
int b = 2;
int c = 3;

initial begin
	int d = {<<{a, b, c}};
end

endmodule
