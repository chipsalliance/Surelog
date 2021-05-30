// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: implements_extends
:description: class both implementing and extending
:tags: 8.26.2
*/
module class_tb ();
	interface class ihello;
		pure virtual function void hello();
	endclass

	interface class itest;
		pure virtual function void test();
	endclass

	class base;
		function method();
			$display("method");
		endfunction
	endclass
	
	class Hello extends base implements ihello, itest;
		virtual function void hello();
			$display("hello world");
		endfunction
		virtual function void test();
			$display("test");
		endfunction
	endclass

	Hello obj;

	initial begin
		obj = new;
		obj.method();
		obj.hello();
		obj.test();
	end
endmodule
