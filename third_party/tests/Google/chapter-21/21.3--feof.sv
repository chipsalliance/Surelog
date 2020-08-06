/*
:name: feof_function
:description: $feof test
:tags: 21.3
:type: simulation parsing
*/
module top();

initial begin
	int fd;
	fd = $fopen("tmp.txt", "w");
	$display($feof(fd));
	$fclose(fd);
end

endmodule
