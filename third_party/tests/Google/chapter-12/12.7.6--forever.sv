// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: forever_loop
:description: A module testing forever loop
:tags: 12.7.6
*/
module foreach_tb ();
   initial begin
      forever begin : loop
	 disable loop;
      end
   end
endmodule
