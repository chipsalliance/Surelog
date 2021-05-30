// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: iface_class_test_9
:description: Test
:tags: 8.3 8.26
*/
typedef int arg_type;

interface class base_ic;
pure virtual task pure_task1;
pure virtual task pure_task2(arg_type arg);
endclass

module test;
endmodule
