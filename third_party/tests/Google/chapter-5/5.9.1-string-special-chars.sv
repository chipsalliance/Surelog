// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: string-special-chars
:description: Special characters in strings
:tags: 5.9.1
*/
module top();

  initial begin
    $display("newline \n");
    $display("tab \t");
    $display("backslash \\");
    $display("quote \"");
    $display("vertical tab \v");
    $display("form feed \f");
    $display("bell \a");
    $display("octal \123");
    $display("hex \x12");
  end

endmodule
