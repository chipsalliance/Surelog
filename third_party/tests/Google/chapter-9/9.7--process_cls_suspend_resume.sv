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
				automatic int k = j;
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
