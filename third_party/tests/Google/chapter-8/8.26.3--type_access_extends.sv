// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: type_access_extends
:description: accessing types from extended interface class
:tags: 8.26.3
*/
module class_tb ();
	interface class ihello;
		typedef int int_t;
		pure virtual function void hello(int_t val);
	endclass

	interface class ihello_ex extends ihello;
		pure virtual function void hello_ex(int_t v1, int_t v2);
	endclass
endmodule
