/*
:name: file_tasks
:description: $fopen and $fclose test
:should_fail: 0
:tags: 21.3
:type: simulation parsing
*/
module top();

initial begin
	int fd;
	fd = $fopen("tmp.txt", "w");
	$fclose(fd);
end

endmodule
