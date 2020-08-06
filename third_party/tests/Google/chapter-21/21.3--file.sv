/*
:name: file_tasks
:description: $fopen and $fclose test
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
