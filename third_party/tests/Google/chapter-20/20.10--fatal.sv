/*
:name: fatal_task
:description: $fatal test
:tags: 20.10
:type: parsing
  Note this is not a simulation test, as the $warning may result in some
  simulators returning bad exit status.
*/

module top();

initial begin
	$fatal(2, "fatal");
end

endmodule
