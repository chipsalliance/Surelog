module test;

    event e_Peek;
    reg	  r_Poke;

    initial begin
	// $dumpvars;
	#0;
	r_Poke = 0;
	#50 $finish;
    end

    always @(r_Poke) begin
	$display("r_Poke recieved @ %0t", $time);
	#10;
	$display("e_Peek asserted @ %0t", $time);
	->e_Peek;
    end

endmodule
