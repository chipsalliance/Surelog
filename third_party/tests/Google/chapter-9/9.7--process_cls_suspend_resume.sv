// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: process_control
:description: process control
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
					job[k].suspend();
					$display("process %d", k);
				end
			join_none

		foreach(job[i])
			wait(job[i] != null);

		foreach(job[i])
			job[i].resume();

		job[1].await();

		foreach(job[i])
			if(job[i].status != process::FINISHED)
				job[i].kill();
	endtask

	initial begin
		test(8);
	end

endmodule
