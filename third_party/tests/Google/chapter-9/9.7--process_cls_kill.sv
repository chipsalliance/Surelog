// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: process_cls_kill
:description: process class kill method
:tags: 9.7
*/
module process_tb ();
	task automatic test (int N);
		process job[] = new [N];

		foreach(job[i])
			fork
				automatic int k = i;
				begin
					job[k] = process::self();
					$display("process %d", k);
				end
			join_none

		foreach(job[i])
			wait(job[i] != null);

		job[1].await();

		foreach(job[i])
			if(job[i].status != process::FINISHED)
				job[i].kill();
	endtask

	initial begin
		test(8);
	end

endmodule
