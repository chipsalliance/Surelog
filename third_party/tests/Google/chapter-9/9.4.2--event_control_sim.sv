// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: event_control_simulation
:description: Test event invocation
:tags: 9.4.2
:type: simulation
*/
module top();
   event e;

   int i = 0;

   initial begin
      // For now increment time and order locally only, do some simple checks
      #5;
      i++;
      $display(":assert: (1 == %d)", i);
      $display(":assert: (5 == %d)", $time);

      #5;
      i++;
      $display(":assert: (2 == %d)", i);
      $display(":assert: (10 == %d)", $time);

      // Run event a, i should be incremented inside that event
      #2;
      ->e;

      // i is not incremented until the next delay
      $display(":assert: (2 == %d)", i);
      // but time already is
      $display(":assert: (12 == %d)", $time);
      #3;

      $display(":assert: (3 == %d)", i);
      $display(":assert: (15 == %d)", $time);

      $finish;
   end

   always @ (e) begin
      i++;
   end
endmodule
