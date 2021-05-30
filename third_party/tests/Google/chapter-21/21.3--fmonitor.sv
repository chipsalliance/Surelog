// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: fmonitor_task
:description: $fmonitor test
:tags: 21.3
:type: simulation parsing
*/
module top();

logic a;

int fd;
string str = "abc";

initial begin
	fd = $fopen("tmp.txt", "w");
	$fmonitor(fd, a);
	$fmonitorb(fd, a);
	$fmonitoro(fd, a);
	$fmonitorh(fd, a);
end

final
	$fclose(fd);

endmodule
