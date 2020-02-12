/*
:name: fwrite_boh
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
	$fwriteb(fd, str);
	$fwriteo(fd, str);
	$fwriteh(fd, str);
end

final
	$fclose(fd);

endmodule
