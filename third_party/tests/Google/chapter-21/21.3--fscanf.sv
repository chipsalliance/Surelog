/*
:name: fscanf_task
:description: $fscanf test
:tags: 21.3
:type: simulation parsing
*/
module top();

int fd;
int c;

initial begin
	fd = $fopen("tmp.txt", "w");
	$fscanf(fd, "%d", c);
end

final
	$fclose(fd);

endmodule
