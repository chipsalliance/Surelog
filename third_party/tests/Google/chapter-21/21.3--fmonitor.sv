/*
:name: fmonitor_task
:description: $fmonitor test
:tags: 21.3
:type: simulation parsing
*/
module top();

logic a;

int fd;
string str = "abc";

initial begin
	fd = $fopen("tmp.txt", "w");
	$fmonitor(fd, a);
	$fmonitorb(fd, a);
	$fmonitoro(fd, a);
	$fmonitorh(fd, a);
end

final
	$fclose(fd);

endmodule
