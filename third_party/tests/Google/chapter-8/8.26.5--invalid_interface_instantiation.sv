// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: interface_instantiation
:description: instantiating an interface class
:should_fail_because: instantiating an interface class
:tags: 8.26.5
:type: simulation
*/
module class_tb ();
	interface class ihello;
		pure virtual function void hello();
	endclass
	
	ihello obj;

	initial begin
		obj = new;
	end
endmodule
