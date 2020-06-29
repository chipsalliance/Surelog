/*
:name: process_cls_await
:description: process class await method
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
					$display("process %d", k);
				end
			join_none

		foreach(job[i])
			wait(job[i] != null);

		job[1].await();
	endtask

	initial begin
		test(8);
	end

endmodule
