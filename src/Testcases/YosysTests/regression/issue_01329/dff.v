// Design
// D flip-flop
// https://www.edaplayground.com/x/5dzJ

// If (asynchronous 'reset_sync' & enable') are true on the same clock, 
// and then 'reset_sync' is low on the next clock,
// then the asynchronous 'reset_sync' gets ignored and the 'enable' applied

module dff (clk, reset, enable, d, q);
	  
	input      clk;
	input      reset;
	input 	 enable;
	input      d;
	output reg q;


  	always @(posedge clk or posedge reset_sync)
  	begin
    	if (reset_sync) begin
      		// Asynchronous reset when reset goes high
	      	q <= 1'b0;      
	    end 

		else if(enable) 
		begin
      		// Assign D to Q on positive clock edge
      		q <= d;
    	end
  	end

	wire reset_sync;

    synchronizer #(.RESET_STATE(1)) reset_synchronizer(
        .clk(clk),
        .reset(reset),
        .data_i(0),
        .data_o(reset_sync));


`ifdef FORMAL

	always @($global_clock) assume(clk != $past(clk));

	localparam MAX_CNT = 16;

	reg[$clog2(MAX_CNT)-1:0] counter;
	initial counter = 0;

	always @(posedge clk) counter <= counter + 1;

	initial assume(reset);
	initial assume(enable);

	always @(posedge clk) if(counter == (MAX_CNT >> 1)) assume(reset != $past(reset));


	//always @(*) assume(d == 1'b1);

	always @(clk) 
	begin
		if(clk) assume(d == 1'b0); 
		
		else assume(d == 1'b1);
	end

	always @(clk) 
	begin
		if(clk) assume(!enable); 
		
		else assume(enable);
	end

	always @(posedge clk) 
	begin
		if(reset_sync) assert(q == 0);

		else if(enable) assert(q == d);

		else assert(q == $past(q));
	end

	always @(posedge clk) cover(reset && enable && d && !clk);

`endif

endmodule
