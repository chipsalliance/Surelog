/*
:name: ferror_function
:description: $ferror test
:tags: 21.3
:type: simulation parsing
*/
module top();

initial begin
	int fd;
	string str;
	integer errno;
	fd = $fopen("tmp.txt", "w");
	errno = $ferror(fd, str);
	$display(errno);
	$display(str);
	$fclose(fd);
end

endmodule
