// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: class_test_58
:description: Test
:tags: 6.15 8.3
*/
typedef int data_type_or_module_type;

class fields_with_modifiers;
  const static data_type_or_module_type foo1 = 4'hf;
  static const data_type_or_module_type foo3 = 1, foo4 = 2;
endclass

module test;
endmodule
