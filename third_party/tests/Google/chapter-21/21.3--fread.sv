// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: fread_task
:description: $fread test
:tags: 21.3
:type: simulation parsing
*/
module top();

int fd;
int c;

initial begin
	fd = $fopen("tmp.txt", "w");
	$fread(c, fd);
end

final
	$fclose(fd);

endmodule
