/*
:name: ungetc_function
:description: $ungetc test
:tags: 21.3
:type: simulation parsing
*/
module top();

int fd;

initial begin
	fd = $fopen("tmp.txt", "w");
	$ungetc(123, fd);
	$display(":assert: (%d == %d)", 123, $fgetc(fd));
end

final
	$fclose(fd);

endmodule
