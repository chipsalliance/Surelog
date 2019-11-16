/*
:name: fgetc_function
:description: $fgetc test
:should_fail: 0
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
