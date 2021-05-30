// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: ungetc_function
:description: $ungetc test
:tags: 21.3
:type: simulation parsing
*/
module top();

int fd;

initial begin
	fd = $fopen("tmp.txt", "w");
	$ungetc(123, fd);
	$display(":assert: (%d == %d)", 123, $fgetc(fd));
end

final
	$fclose(fd);

endmodule
