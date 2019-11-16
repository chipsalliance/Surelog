
//`timescale 1 ns / 1 ps
module testbench;

parameter pclk = 5;         /// period of clk/2 
parameter max_number = 10;  /// number of input codewords in file
parameter number = 2;       /// number of input codewords to use

reg clk,reset;
reg CE;
reg [7:0] input_byte;

wire [7:0] Out_byte;
wire CEO;
wire Valid_out;

RS_dec  DUT 
(
  .clk(clk), // input clock 
  .reset(reset), // active high asynchronous reset
  .CE(CE), // chip enable active high flag for one clock with every input byte
  .input_byte(input_byte), // input byte
  
  .Out_byte(Out_byte),   // output byte
  .CEO(CEO),  // chip enable for the next block will be active high for one clock , every 8 clks
  .Valid_out(Valid_out) /// valid out for every output block (188 byte)
);



reg [7:0] in_mem [0:(max_number*204)-1];
reg [7:0] out_mem [0:(max_number*188)-1];

reg enable;
reg [7:0]true_out;
integer h,k,err;


initial
begin
	clk=0;
	forever #pclk clk=~clk;
end 



integer ce_t,in_t;
integer lim; // minimum  6

initial 
begin
	err=0;
	lim=6;
	$readmemb("reed_solomon_decoder/sim/input.txt",in_mem);
	$readmemb("reed_solomon_decoder/sim/output.txt",out_mem);
end


initial
begin
	CE=0;
	@(posedge enable);
	forever
	begin
		@(posedge clk);
		#2 CE=1;
		@(posedge clk);
		#2 CE=0;
		for(ce_t=0; ce_t<lim; ce_t=ce_t+1)
			@(posedge clk); 
	end 
end

initial 
begin
	h=0;
	k=0;
	enable = 0;
	reset =1;
	@(posedge clk); @(posedge clk); @(posedge clk);
	@(posedge clk); @(posedge clk); @(posedge clk);
	reset=0;
	@(posedge clk); @(posedge clk);
	enable=1;
end

initial
begin
	// $dumpfile("bench.vcd");
	// repeat (5) @(posedge clk);
	// $dumpvars(0, testbench);
	// repeat (800) @(posedge clk);
	// $write("\n");
	// $finish;
end

///////////////////// inputs///////////////

reg write_input_progress = 1;

initial 
begin

	input_byte=0;
	
	@(posedge enable);

	for(k=0;k<(number*204);k=k+1)
	begin
		if (write_input_progress) begin
			if (k % 50 == 0 && k != 0)
				$write("\n");
			$write(".");
			$fflush;
		end

		input_byte=in_mem[k];
		
		@(posedge clk);@(posedge clk);
		for(in_t=0; in_t < lim; in_t=in_t+1)
			@(posedge clk); 
	end 

end

//////////////////////////////outputs////////////////////////
always @ (posedge(clk))
begin
	if(Valid_out && CEO)
		begin
			true_out = out_mem[h];

			if (write_input_progress) begin
				write_input_progress = 0;
				$write("\n");
			end

			if (h % 10 == 0)
				$write("%d ", h);
			$write(" %x %x", true_out, Out_byte);
			if (h % 10 == 9)
				$write("\n");
			
			if(true_out !== Out_byte)
				begin
					$display("Error at out no. %d !!!!!!!!!!!!!",h);
					err=err+1;
				end
			h=h+1;
			
			if(h== (number*188) )
				begin
					if (h % 10 != 0)
						$write("\n");
					if (err == 0)
						$display("Test OK.");
					else
						$display("Total Errors =  %d !!!!!!!!!!!!!",err);
						
					$finish;
				end
			
		end
end

endmodule
