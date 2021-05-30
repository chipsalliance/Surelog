// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: event_control_simulation_minimal
:description: Test event invocation
:tags: 9.4.2
:type: simulation
*/
module top();
   event e;

   int i = 0;

   initial begin
      $display(":assert: (0 == %d)", i);
      $display(":assert: (0 == %d)", $time);

      ->e;

      #5;

      $display(":assert: (1 == %d)", i);
      $display(":assert: (5 == %d)", $time);

      $finish;
   end

   always @ (e) begin
      i++;
   end
endmodule
