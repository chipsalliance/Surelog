/*
:name: fgets_function
:description: $fgets test
:tags: 21.3
:type: simulation parsing
*/
module top();

int fd;
string tmp;

initial begin
	fd = $fopen("tmp.txt", "w");
	$fgets(tmp, fd);
end

final
	$fclose(fd);

endmodule
