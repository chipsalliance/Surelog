// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: implements
:description: implements keyword test
:tags: 8.26.2
*/
module class_tb ();
	interface class ihello;
		pure virtual function void hello();
	endclass
	
	class Hello implements ihello;
		virtual function void hello();
			$display("hello world");
		endfunction
	endclass

	Hello obj;

	initial begin
		obj = new;
		obj.hello();
	end
endmodule
