/*
:name: fgetc_function
:description: $fgetc test
:tags: 21.3
:type: simulation parsing
*/
module top();

int fd;
int c;

initial begin
	fd = $fopen("tmp.txt", "w");
	c = $fgetc(fd);
end

final
	$fclose(fd);

endmodule
