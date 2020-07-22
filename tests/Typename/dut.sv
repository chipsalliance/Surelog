module top();

initial begin
	$display(":assert: ('%s' == 'logic')", $typename(logic));
	$display(":assert: ('%s' == 'logic')", $typename(int));
	$display(":assert: ('%s' == 'logic')", $typename(a));
end

endmodule

