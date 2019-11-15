// altera verilog_input_version SystemVerilog_2005

/*
  Legal Notice: (C)2007 Altera Corporation. All rights reserved.  Your
  use of Altera Corporation's design tools, logic functions and other
  software and tools, and its AMPP partner logic functions, and any
  output files any of the foregoing (including device programming or
  simulation files), and any associated documentation or information are
  expressly subject to the terms and conditions of the Altera Program
  License Subscription Agreement or other applicable license agreement,
  including, without limitation, that your use is for the sole purpose
  of programming logic devices manufactured by Altera and sold by Altera
  or its authorized distributors.  Please refer to the applicable
  agreement for further details.
*/

/*

	Author:  JCJB
	Date:  01/28/2008
	
	This block contains a FIR filter capable of the following:
	
	- 4/8/16 symetrical taps
	- parameterizable FIFO depth
	- Avalon-ST integration
	
	This hardware has not been optimized for targeting DSP blocks
	or memory.  It is recommended to replace the multipliers with
	memory multiplications.
	
	The register "tag" is used to perform flow control to avoid overflowing
	the output FIFO.  For every data sample that enters the filter, five clock
	cycles of latency will occur before the result is stuffed into the FIFO.
	If the amount of pipelining changes so must the tap width used to track valid
	data through the pipeline of adders and multipliers.  This filter supports
	clearing functionality as well if a new data stream is provided at the input.
*/

module custom_FIR (
	clk,
	reset,

	// the "sink" side
	sink_data,
	sink_valid,
	sink_ready,

	// the "source" side
	source_data,
	source_valid,
	source_ready,
	
	clear
);

	parameter DATA_WIDTH = 16;  // input data width (output is wider)
	parameter COEF_WIDTH = 8;
	parameter NUM_OF_TAPS = 16;  // use only an even number of taps of 4, 8, or 16 (for now)
	parameter SYMMETRIC = 1;  // unused right now, this would either use "NUM_OF_TAPS"/2 multipliers when 1 otherwise "NUM_OF_TAPS" multipliers (un-implemented)
	parameter FIFO_DEPTH = 32;  // make sure this is at least 32
  parameter FIFODEPTH_LOG2 = 5; //log2 of the FIFO_DEPTH
  
	input clk;
	input reset;
	

	// the "sink" side
	input signed [DATA_WIDTH-1:0] sink_data;
	input sink_valid;
	output wire sink_ready;


	// the "source" side
	output wire [(DATA_WIDTH + COEF_WIDTH + 1):0] source_data;
	output wire source_valid;
	input source_ready;


	input clear;
	

	// the internal registers, after taps there are 4 stages of pipelining
	reg signed [DATA_WIDTH-1:0] taps [NUM_OF_TAPS-1:0];
	reg signed [DATA_WIDTH:0] initial_additions [(NUM_OF_TAPS/2)-1:0];  // addition between two taps, only used in symetric filters
	reg signed [DATA_WIDTH+COEF_WIDTH:0] multiplications [(NUM_OF_TAPS/2)-1:0]; // initial_additions * coefficients
	reg signed [DATA_WIDTH+COEF_WIDTH+1:0] final_additions [(NUM_OF_TAPS/4)-1:0];  // two multiply results added together and registered
	reg signed [DATA_WIDTH+COEF_WIDTH+1:0] final_result;  // sum of final_additions
	wire signed [DATA_WIDTH+COEF_WIDTH+1:0] final_result_temp;
	wire signed [COEF_WIDTH-1:0] coefficients [0: (NUM_OF_TAPS/2) -1];

	reg [4:0] tag;  // shift register that tracks the valid data moving through the adders and multipliers


	// other misc. control signal
	wire read_fifo;
	wire pipeline_enable;
	wire fifo_empty;
	wire fifo_half_full;

	assign coefficients = '{ `include "coefs.h" };

/**********************************************************************************
 TAP PIPELINE
 **********************************************************************************/
	always @ (posedge clk or posedge reset)
	begin
		if (reset)
		begin
			taps[0] <= 0;
		end
		else if (clear == 1)
		begin
			taps[0] <= 0;
		end
		else if (pipeline_enable == 1)
		begin
			taps[0] <= sink_data;
		end
	end	
	
	genvar tap_counter;
	generate
	for(tap_counter = 1; tap_counter < NUM_OF_TAPS; tap_counter = tap_counter+1)
	begin : the_taps
		always @ (posedge clk or posedge reset)
		begin
			if (reset)
			begin
				taps[tap_counter] <= 0;
			end
			else if (clear == 1)
			begin
				taps[tap_counter] <= 0;
			end
			else if (pipeline_enable == 1)
			begin
				taps[tap_counter] <= taps[tap_counter-1];
			end
		end
	end
	endgenerate
/**********************************************************************************/	


/**********************************************************************************
 INITIAL ADDER PIPELINE
 **********************************************************************************/
	genvar initial_add_counter;
	generate
	for(initial_add_counter = 0; initial_add_counter < (NUM_OF_TAPS/2); initial_add_counter=initial_add_counter+1)
	begin : the_initial_adds
		always @ (posedge clk or posedge reset)
		begin
			if (reset)
			begin
				initial_additions[initial_add_counter] <= 0;
			end
			else if (clear == 1)
			begin
				initial_additions[initial_add_counter] <= 0;
			end
			else
			begin
				initial_additions[initial_add_counter] <= taps[initial_add_counter] + taps[NUM_OF_TAPS - 1 - initial_add_counter];
			end
		end
	end
	endgenerate
/**********************************************************************************/



/**********************************************************************************
 MULTIPLIER PIPELINE
 **********************************************************************************/
	genvar multiplier_counter;
	generate
	for(multiplier_counter = 0; multiplier_counter < (NUM_OF_TAPS/2); multiplier_counter=multiplier_counter+1)
	begin : the_multipliers
		always @ (posedge clk or posedge reset)
		begin
			if (reset)
			begin
				multiplications[multiplier_counter] <= 0;
			end
			else if (clear == 1)
			begin
				multiplications[multiplier_counter] <= 0;
			end
			else
			begin
				multiplications[multiplier_counter] <= initial_additions[multiplier_counter] * coefficients[multiplier_counter];
			end
		end
	end
	endgenerate
/**********************************************************************************/



/**********************************************************************************
 FINAL ADDER PIPELINE
 **********************************************************************************/
	genvar final_add_counter;
	generate
	for(final_add_counter = 0; final_add_counter < (NUM_OF_TAPS/4); final_add_counter=final_add_counter+1)
	begin : the_final_adds
		always @ (posedge clk or posedge reset)
		begin
			if (reset)
			begin
				final_additions[final_add_counter] <= 0;
			end
			else if (clear == 1)
			begin
				final_additions[final_add_counter] <= 0;
			end
			else
			begin
				final_additions[final_add_counter] <= multiplications[2*final_add_counter] + multiplications[(2*final_add_counter)+1];
			end
		end
	end
	endgenerate
/**********************************************************************************/



/**********************************************************************************
 FINAL RESULT PIPELINE
 **********************************************************************************/
	generate
		if(NUM_OF_TAPS == 4)
			assign final_result_temp = final_additions[0];
		else if (NUM_OF_TAPS == 8)
			assign final_result_temp = final_additions[0] + final_additions[1];
		else if (NUM_OF_TAPS == 16)
			assign final_result_temp = final_additions[0] + final_additions[1] + final_additions[2] + final_additions[3];
	endgenerate  // after 16 taps this should addition should be done with registered stages
	
	always @ (posedge clk or posedge reset)
	begin
		if (reset)
		begin
			final_result <= 0;
		end
		else if (clear == 1)
		begin
			final_result <= 0;
		end
		else
		begin
			final_result <= final_result_temp;
		end
	end
/**********************************************************************************/



/**********************************************************************************
 OUTPUT FIFO AND SYNC LOGIC (used for backpressure purposes)
 **********************************************************************************/
	assign sink_ready = (fifo_half_full == 0);
	assign pipeline_enable = (sink_ready == 1) & (sink_valid == 1);

	assign source_valid = (fifo_empty == 0);
	assign read_fifo = (source_valid == 1) & (source_ready == 1);

	always @ (posedge clk or posedge reset)
	begin
		if (reset)
		begin
			tag <= 0;
		end
		else if (clear == 1)
		begin
			tag <= 0;
		end
		else
		begin
			tag <= {tag[3:0], pipeline_enable}; 
		end
	end



	scfifo the_output_fifo (
		.aclr (reset),
		.sclr (clear),
		.clock (clk),
		.data (final_result),
		.almost_full (fifo_half_full),
		.empty (fifo_empty),
		.q (source_data),
		.rdreq (read_fifo),
		.wrreq (tag[4])  // tag delay pipeline matches when valid data pops out of "final_result"
	);
	defparam the_output_fifo.LPM_WIDTH = DATA_WIDTH+COEF_WIDTH+2;
	defparam the_output_fifo.LPM_NUMWORDS = FIFO_DEPTH;
	
	defparam the_output_fifo.LPM_WIDTHU = FIFODEPTH_LOG2;
	
	defparam the_output_fifo.ALMOST_FULL_VALUE = FIFO_DEPTH - 2 - 6;  // -2 for the FIFO latency, and -6 for the pipelining latency of the FIR operation with room to spare
	defparam the_output_fifo.LPM_SHOWAHEAD = "ON";
	defparam the_output_fifo.USE_EAB = "ON";
	defparam the_output_fifo.ADD_RAM_OUTPUT_REGISTER = "OFF";
	defparam the_output_fifo.UNDERFLOW_CHECKING = "OFF";
	defparam the_output_fifo.OVERFLOW_CHECKING = "OFF";
/**********************************************************************************/


endmodule
