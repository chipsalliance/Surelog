/*
:name: forever_loop
:description: A module testing forever loop
:tags: 12.7.6
*/
module foreach_tb ();
   initial begin
      forever begin : loop
	 disable loop;
      end
   end
endmodule
