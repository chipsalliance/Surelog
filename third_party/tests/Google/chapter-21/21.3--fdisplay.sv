/*
:name: fdisplay_task
:description: $fdisplay test
:tags: 21.3
:type: simulation parsing
*/
module top();

int fd;
string str = "abc";

initial begin
	fd = $fopen("tmp.txt", "w");
	$fdisplay(fd, str);
end

final
	$fclose(fd);

endmodule
