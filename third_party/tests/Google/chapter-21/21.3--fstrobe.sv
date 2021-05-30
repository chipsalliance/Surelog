// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: fstrobe_task
:description: $fstrobe test
:tags: 21.3
:type: simulation parsing
*/
module top();

logic clk;
logic a;

int fd;

always @(posedge clk) begin
	$fstrobe(fd, a);
	$fstrobe(fd, a);
	$fstrobe(fd, a);
	$fstrobe(fd, a);
end

initial begin
	fd = $fopen("tmp.txt", "w");
end

final
	$fclose(fd);

endmodule
