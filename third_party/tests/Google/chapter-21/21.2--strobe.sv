/*
:name: strobe_task
:description: $strobe test
:tags: 21.2
:type: simulation parsing
*/
module top();

logic clk;
int a;

always @(posedge clk) begin
	$strobe(a);
	$strobeb(a);
	$strobeo(a);
	$strobeh(a);
end

endmodule
