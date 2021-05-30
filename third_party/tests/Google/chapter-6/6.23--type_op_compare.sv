// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: type_op_compare
:description: type comparison tests
:tags: 6.23
*/
module top #( parameter type T = type(logic[11:0]) )
   ();
   initial begin
      case (type(T))
        type(logic[11:0]) : ;
        default           : $stop;
      endcase
      if (type(T) == type(logic[12:0])) $stop;
      if (type(T) != type(logic[11:0])) $stop;
      if (type(T) === type(logic[12:0])) $stop;
      if (type(T) !== type(logic[11:0])) $stop;
      $finish;
   end
endmodule
