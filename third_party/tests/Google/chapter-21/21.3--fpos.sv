/*
:name: file_pos_tasks
:description: $fseek, $ftell and $rewind test
:tags: 21.3
:type: simulation parsing
*/
module top();

initial begin
	int fd;
	fd = $fopen("tmp.txt", "w");
	$display(":assert: (%d == 0)", $ftell(fd));
	$fseek(fd, 12, 0);
	$display(":assert: (%d == 12)", $ftell(fd));
	$rewind(fd);
	$display(":assert: (%d == 0)", $ftell(fd));
	$fclose(fd);
end

endmodule
