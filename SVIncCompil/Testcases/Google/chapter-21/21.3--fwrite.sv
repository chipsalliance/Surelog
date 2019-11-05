/*
:name: fwrite_task
:description: $fwrite test
:should_fail: 0
:tags: 21.3
:type: simulation parsing
*/
module top();

int fd;
string str = "abc";

initial begin
	fd = $fopen("tmp.txt", "w");
	$fwrite(fd, str);
	$fwriteb(fd, str);
	$fwriteo(fd, str);
	$fwriteh(fd, str);
end

final
	$fclose(fd);

endmodule
