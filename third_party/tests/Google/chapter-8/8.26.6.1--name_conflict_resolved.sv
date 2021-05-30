// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: name_conflict_resolved
:description: resolved interface class method name conflict
:tags: 8.26.6.1
:type: simulation parsing
*/
module class_tb ();
	interface class ihello;
		pure virtual function void hello();
	endclass

	interface class itest;
		pure virtual function void hello();
	endclass
	
	class Hello implements ihello, itest;
		virtual function void hello();
			$display(":assert:(True)");
		endfunction
	endclass

	Hello obj;

	initial begin
		obj = new;
		obj.hello();
	end
endmodule
