// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: fatal_task
:description: $fatal test
:tags: 20.10
:type: parsing
  Note this is not a simulation test, as the $warning may result in some
  simulators returning bad exit status.
*/

module top();

initial begin
	$fatal(2, "fatal");
end

endmodule
