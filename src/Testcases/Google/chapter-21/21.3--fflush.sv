/*
:name: fflush_task
:description: $fflush test
:should_fail: 0
:tags: 21.3
:type: simulation parsing
*/
module top();

initial begin
	int fd;
	fd = $fopen("tmp.txt", "w");
	$fflush();
	$fclose(fd);
end

endmodule
