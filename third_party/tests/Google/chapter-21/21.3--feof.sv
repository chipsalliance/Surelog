// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: feof_function
:description: $feof test
:tags: 21.3
:type: simulation parsing
*/
module top();

initial begin
	int fd;
	fd = $fopen("tmp.txt", "w");
	$display($feof(fd));
	$fclose(fd);
end

endmodule
