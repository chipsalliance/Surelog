/*
:name: fdisplay_boh
:description: $fdisplay test
:tags: 21.3
:type: simulation parsing
*/
module top();

int fd;
string str = "abc";

initial begin
	fd = $fopen("tmp.txt", "w");
	$fdisplayb(fd, str);
	$fdisplayo(fd, str);
	$fdisplayh(fd, str);
end

final
	$fclose(fd);

endmodule
