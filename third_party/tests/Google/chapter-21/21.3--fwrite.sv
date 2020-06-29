/*
:name: fwrite_task
:description: $fwrite test
:tags: 21.3
:type: simulation parsing
*/
module top();

int fd;
string str = "abc";

initial begin
	fd = $fopen("tmp.txt", "w");
	$fwrite(fd, str);
end

final
	$fclose(fd);

endmodule
