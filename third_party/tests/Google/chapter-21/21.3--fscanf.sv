// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: fscanf_task
:description: $fscanf test
:tags: 21.3
:type: simulation parsing
*/
module top();

int fd;
int c;

initial begin
	fd = $fopen("tmp.txt", "w");
	$fscanf(fd, "%d", c);
end

final
	$fclose(fd);

endmodule
