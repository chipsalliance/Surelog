/*
:name: fflush_task
:description: $fflush test
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
