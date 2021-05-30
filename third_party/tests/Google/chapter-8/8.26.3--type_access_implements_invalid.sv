// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: type_access_implements_invalid
:description: access types from implemented class
:should_fail_because: typedefs are not inherited by implements operator
:tags: 8.26.3
:type: simulation
*/
module class_tb ();
	interface class ihello;
		typedef int int_t;
		pure virtual function void hello(int_t val);
	endclass
	
	class Hello implements ihello;
		virtual function void hello(int_t val);
			$display("hello world %d", val);
		endfunction
	endclass

	Hello obj;

	initial begin
		obj = new;
		obj.hello();
	end
endmodule
