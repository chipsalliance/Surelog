/*
 * Copyright (c) 2002 Stephen Williams (steve@icarus.com)
 *
 *    This source code is free software; you can redistribute it
 *    and/or modify it in source code form under the terms of the GNU
 *    General Public License as published by the Free Software
 *    Foundation; either version 2 of the License, or (at your option)
 *    any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

/*
 * This test tests simple zero-extend of small r-values into large
 * l-values. Notice how x values are an exception.
 */
module main;

   reg [3:0] y;
   reg 	     x;

   initial begin
      x = 1'b0;
      y = x;
      if (y !== 4'b0000) begin
	 $display("FAILED -- x=%b, y=%b", x, y);
	 $finish;
      end

      x = 1'b1;
      y = x;
      if (y !== 4'b0001) begin
	 $display("FAILED -- x=%b, y=%b", x, y);
	 $finish;
      end

      x = 1'bx;
      y = x;
      if (y !== 4'bxxxx) begin
	 $display("FAILED -- x=%b, y=%b", x, y);
	 $finish;
      end

      x = 1'bz;
      y = x;
      if (y !== 4'b000z) begin
	 $display("FAILED -- x=%b, y=%b", x, y);
	 $finish;
      end

      $display("PASSED");
   end // initial begin

endmodule // main
