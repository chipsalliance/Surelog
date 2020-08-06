/*
:name: monitor_task
:description: $monitor test
:tags: 21.2
:type: simulation parsing
*/
module top();

int a;

initial begin
	$monitoron;
	$monitor(a);
	$monitorb(a);
	$monitoro(a);
	$monitorh(a);
	$monitoroff;
end

endmodule
