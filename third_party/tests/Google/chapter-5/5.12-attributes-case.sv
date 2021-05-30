// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: attributes-case
:description: Assing attributes to a case statement
:tags: 5.12
*/

module top();
  reg [1:0] a;

  bit b;

  initial begin;

    (* full_case, parallel_case *)
    case (a)
      2'b00 :
        b = 0;
      2'b01, 2'b10 :
        b = 1;
      default :
        b = 0;
    endcase

    (* full_case = 1 *)
    (* parallel_case = 1 *)
    case (a)
      2'b00 :
        b = 0;
      2'b01, 2'b10 :
        b = 1;
      default :
        b = 0;
    endcase

    (* full_case, parallel_case = 0 *)
    case (a)
      2'b00 :
        b = 0;
      2'b01, 2'b10 :
        b = 1;
      default :
        b = 0;
    endcase

  end

endmodule
