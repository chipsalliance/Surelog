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
	Date:  11/04/2007
	
	This DMA channel connects a read and write master together using a block
	called the transform block.  In the case of this DMA the transform block is
	simply wires.  The slave port is used to start transfers and collect the status
	of the DMA.  The register maps is as follows:
	
	Byte Offset	|	Name	
	------------------------
		0			Status
		4			Read Address (Word Aligned)
		8			Write Address (Word Aligned)
		C			Length (Bytes)
		10			N/A
		14			N/A
		18			Control
		1C			N/A
	
	Status Register:
	
	  Bit 0 --> Done (DMA has completed transfer)
	  Bit 1 --> Busy (DMA is currently tranfering data)
	  
	  Write to status register to clears
	
	
	Read Address Register (32 bits):
	
	  Read location specified in bytes.  This location must be word aligned.
	
	
	Write Address Register (32 bits):
	
	  Write location specified in bytes.  This location must be word aligned.
	
	
	Length Register (32 bits):
	
	  Number of bytes to be transfered.  Must be a multiple of the word width in bytes.
	  This ensures the last transfer location is lined up on a word boundary.
	
	
	Control Register:
	
	Bit 3 --> Go (starts transfer)
	Bit 4 --> I_EN (enable interrupt when all writes complete)
	Bit 8 --> RCON (read from a fixed location)
	Bit 9 --> WCON (write to a fixed location)
	
	
	The transfer block used in this DMA can be replaced with any transformation logic.  You
	must simply ensure that the transfom block does not read from the read master FIFO when it
	is empty or write to the write master FIFO when it is full.  The interface for the transform
	block is as follows:
	
	Read Master			Transform Block			Write Master
	
	transform_readdata --------->
	transform_data_available --->
	transform_read <-------------
	
								----------> transform_writedata
								----------> transform_write
								<---------- transform_wait
	
	To replace the transform simply modify or replace the file called transform_block.v
*/	


module pipelined_read_burst_write_dma (
	clk,
	reset,
	
	// control port interface
	slave_address,
	slave_writedata,
	slave_write,
	slave_read,
	slave_byteenable,
	slave_readdata,
	slave_irq,	
	
	// read master port interface
	read_master_address,
	read_master_read,
	read_master_byteenable,
	read_master_readdata,
	read_master_readdatavalid,
	read_master_waitrequest,
	
	// write master port interface
	write_master_address,
	write_master_write,
	write_master_byteenable,
	write_master_writedata,
	write_master_burstcount,
	write_master_waitrequest
);

	// global settings
	parameter DATAWIDTH = 32;
	parameter BYTEENABLEWIDTH = 4;
	parameter ADDRESSWIDTH = 32;  // address width of the master address signal
	parameter FIFOUSEMEMORY = 1;  // set to use to use LEs instead

	// read master settings
	parameter READ_FIFODEPTH = 32;
	parameter READ_FIFODEPTH_LOG2 = 5;


	// write master settings
	parameter WRITE_FIFODEPTH = 32;
	parameter WRITE_FIFODEPTH_LOG2 = 5;
	parameter WRITE_MAXBURSTCOUNT = 4;
	parameter WRITE_MAXBURSTCOUNT_WIDTH = 3;


	input clk;
	input reset;


	// control port interface
	input [2:0] slave_address;
	input [31:0] slave_writedata;
	input slave_write;
	input slave_read;  // this isn't used, maybe register control_readdata and use this as the enable
	input [3:0] slave_byteenable;
	output wire [31:0] slave_readdata;
	output wire slave_irq;	


	// read master port interface
	output wire [ADDRESSWIDTH-1:0] read_master_address;
	output wire read_master_read;
	output wire [BYTEENABLEWIDTH-1:0] read_master_byteenable;
	input [DATAWIDTH-1:0] read_master_readdata;
	input read_master_readdatavalid;
	input read_master_waitrequest;
	
	
	// write master port interface
	input write_master_waitrequest;
	output wire [ADDRESSWIDTH-1:0] write_master_address;
	output wire write_master_write;
	output wire [BYTEENABLEWIDTH-1:0] write_master_byteenable;
	output wire [DATAWIDTH-1:0] write_master_writedata;
	output wire [WRITE_MAXBURSTCOUNT_WIDTH-1:0] write_master_burstcount;




	// transform block signals (between the read and write masters)
	// read master --> (write)transform(read) --> write master
	wire [DATAWIDTH-1:0] transform_readdata;
	wire transform_read;
	wire transform_data_available;
	wire [DATAWIDTH-1:0] transform_writedata;
	wire transform_write;
	wire transform_wait;
	wire transform_clear;  // if your transform block needs a clear signal (one cycle active high strobe)


	// internal logic signals
	wire control_read_go;
	wire control_write_go;
	wire control_read_done;
	wire control_write_done;
	wire control_read_fixed_address;
	wire control_write_fixed_address;
	wire [ADDRESSWIDTH-1:0] control_read_address;
	wire [ADDRESSWIDTH-1:0] control_read_length;
	wire [ADDRESSWIDTH-1:0] control_write_address;
	wire [ADDRESSWIDTH-1:0] control_write_length;
	wire control_clear;


	
	slave the_slave(
		.clk (clk),
		.reset (reset),
		.slave_address (slave_address),
		.slave_read (slave_read),
		.slave_readdata (slave_readdata),
		.slave_write (slave_write),
		.slave_writedata (slave_writedata),
		.slave_byteenable (slave_byteenable),
		.control_read_go (control_read_go),
		.control_write_go (control_write_go),
		.control_read_done (control_read_done),
		.control_write_done (control_write_done),
		.control_fixed_read_address (control_read_fixed_address),
		.control_read_address (control_read_address),
		.control_read_length (control_read_length),
		.control_fixed_write_address (control_write_fixed_address),
		.control_write_address (control_write_address),
		.control_write_length (control_write_length),
		.control_clear (control_clear),
		.control_irq (slave_irq)
	);
	

	// read master
	latency_aware_read_master the_latency_aware_read_master(
		.clk (clk),
		.reset (reset),
		.control_fixed_location (control_read_fixed_address),
		.control_read_base (control_read_address),
		.control_read_length (control_read_length),
		.control_go (control_read_go),
		.control_done (control_read_done),
		.user_read_buffer (transform_read),
		.user_buffer_data (transform_readdata),
		.user_data_available (transform_data_available),
		.master_address (read_master_address),
		.master_read (read_master_read),
		.master_byteenable (read_master_byteenable),
		.master_readdata (read_master_readdata),
		.master_readdatavalid (read_master_readdatavalid),
		.master_waitrequest (read_master_waitrequest)
	);
	defparam the_latency_aware_read_master.DATAWIDTH = DATAWIDTH;
	defparam the_latency_aware_read_master.BYTEENABLEWIDTH = BYTEENABLEWIDTH;
	defparam the_latency_aware_read_master.ADDRESSWIDTH = ADDRESSWIDTH;
	defparam the_latency_aware_read_master.FIFODEPTH = READ_FIFODEPTH;
	defparam the_latency_aware_read_master.FIFODEPTH_LOG2 = READ_FIFODEPTH_LOG2;
	defparam the_latency_aware_read_master.FIFOUSEMEMORY = FIFOUSEMEMORY;



	// transform block
	transform_block the_transform_block (
		.clk (clk),
		.reset (reset),
		.transform_read (transform_read),
		.transform_readdata (transform_readdata),
		.transform_data_available (transform_data_available),
		.transform_write (transform_write),
		.transform_writedata (transform_writedata),
		.transform_wait (transform_wait),
		.transform_clear (control_clear)
	);
	defparam the_transform_block.DATAWIDTH = DATAWIDTH;



	// write master
	burst_write_master the_burst_write_master (
		.clk (clk),
		.reset (reset),
		.control_fixed_location (control_write_fixed_address),
		.control_write_base (control_write_address),
		.control_write_length (control_write_length),
		.control_go (control_write_go),
		.control_done (control_write_done),
		.user_write_buffer (transform_write),
		.user_buffer_data (transform_writedata),
		.user_buffer_full (transform_wait),
		.master_address (write_master_address),
		.master_write (write_master_write),
		.master_byteenable (write_master_byteenable),
		.master_writedata (write_master_writedata),
		.master_burstcount (write_master_burstcount),
		.master_waitrequest (write_master_waitrequest)
	);
	defparam the_burst_write_master.DATAWIDTH = DATAWIDTH;
	defparam the_burst_write_master.MAXBURSTCOUNT = WRITE_MAXBURSTCOUNT;
	defparam the_burst_write_master.BURSTCOUNTWIDTH = WRITE_MAXBURSTCOUNT_WIDTH;
	defparam the_burst_write_master.BYTEENABLEWIDTH = BYTEENABLEWIDTH;
	defparam the_burst_write_master.ADDRESSWIDTH = ADDRESSWIDTH;
	defparam the_burst_write_master.FIFODEPTH = WRITE_FIFODEPTH;
	defparam the_burst_write_master.FIFODEPTH_LOG2 = WRITE_FIFODEPTH_LOG2;
	defparam the_burst_write_master.FIFOUSEMEMORY = FIFOUSEMEMORY;


endmodule
