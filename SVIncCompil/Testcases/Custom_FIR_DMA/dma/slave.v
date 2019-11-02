/*
  Legal Notice: (C)2008 Altera Corporation. All rights reserved.  Your
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
	Date:  03/18/2008
	
	This Avalon-MM slave module maps the various registers to control signals
	used by the masters of the DMA.  It also handles the interrupt generation.	
*/


module slave (
	// these connect to the clock port
	clk,
	reset,

	// these connect to the slave port
	slave_address,
	slave_read,
	slave_readdata,
	slave_write,
	slave_writedata,
	slave_byteenable,
	
	// these connect to the masters
	control_read_go,
	control_write_go,
	control_read_done,
	control_write_done,
	control_fixed_read_address,
	control_read_address,
	control_read_length,
	control_fixed_write_address,
	control_write_address,
	control_write_length,
	control_clear,
	
	// this connects to the irq sender port
	control_irq
);

	input clk;
	input reset;

	input [2:0] slave_address;
	input slave_read;
	output wire [31:0] slave_readdata;
	input slave_write;
	input [31:0] slave_writedata;
	input [3:0] slave_byteenable;


	output wire control_read_go;
	output wire control_write_go;
	input control_read_done;
	input control_write_done;
	output wire control_fixed_read_address;
	output wire [31:0] control_read_address;
	output wire [31:0] control_read_length;
	output wire control_fixed_write_address;
	output wire [31:0] control_write_address;
	output wire [31:0] control_write_length;
	output wire control_clear;


	output wire control_irq;


	// for internal logic
	reg done_d1;
	wire done_strobe;
	reg [31:0] status_register;
	reg [31:0] read_address_register;
	reg [31:0] write_address_register;
	reg [31:0] length_register;
	reg [31:0] control_register;
	wire [31:0] control_readdata_temp;
	reg [31:0] control_readdata_temp_d1;	
	reg slave_write_d1;
	reg [2:0] slave_address_d1;
	reg [3:0] slave_byteenable_d1;
	
	
	
	
	
/**************************************************************
 Readback path (latency 1)
 **************************************************************/
	assign control_readdata_temp = (slave_address == 3'b000)? status_register :
							  (slave_address == 3'b001)? read_address_register :
							  (slave_address == 3'b010)? write_address_register :
							  (slave_address == 3'b011)? length_register :
							  (slave_address == 3'b110)? control_register : 0;

							
	always @ (posedge clk or posedge reset)
	begin
		if (reset)
		begin
			control_readdata_temp_d1 <= 0;
		end
		else
		begin
			if (slave_read == 1)
			begin
				control_readdata_temp_d1 <= control_readdata_temp;
			end
		end
	end
	
	assign slave_readdata = control_readdata_temp_d1;
/**************************************************************/



/**************************************************************
 Status register (and interrupt)
 **************************************************************/
	always @ (posedge clk or posedge reset)
	begin
		if (reset)
		begin
			status_register <= 0;
		end
		else
		begin
			if (done_strobe == 1)
			begin
				status_register <= 32'h1;  // busy and done
			end
			else if (control_read_go == 1)  // control write go would work too
			begin
				status_register <= 32'h2;  // not busy and not done
			end
			else if ((slave_address == 3'b000) & (slave_write == 1))
			begin
				status_register <= 0;  // clear on write
			end
		end
	end
	
	assign control_irq = status_register[0] & control_register[4]; // done bit of the status register, writing to the status register clears this bit 
/**************************************************************/



/**************************************************************
 Read register
 **************************************************************/
	always @ (posedge clk or posedge reset)
	begin
		if (reset)
		begin
			read_address_register <= 0;
		end
		else
		begin
			if ((slave_address == 3'b001) & (slave_write == 1))
			begin
				if (slave_byteenable[0] == 1)
				begin
					read_address_register[7:0] <= slave_writedata[7:0];
				end
				if (slave_byteenable[1] == 1)
				begin
					read_address_register[15:8] <= slave_writedata[15:8];
				end
				if (slave_byteenable[2] == 1)
				begin
					read_address_register[23:16] <= slave_writedata[23:16];
				end
				if (slave_byteenable[3] == 1)
				begin
					read_address_register[31:24] <= slave_writedata[31:24];
				end		
			end
		end
	end
	
	assign control_read_address = read_address_register;
/**************************************************************/



/**************************************************************
 Write register
 **************************************************************/
	always @ (posedge clk or posedge reset)
	begin
		if (reset)
		begin
			write_address_register <= 0;
		end
		else
		begin
			if ((slave_address == 3'b010) & (slave_write == 1))
			begin
				if (slave_byteenable[0] == 1)
				begin
					write_address_register[7:0] <= slave_writedata[7:0];
				end
				if (slave_byteenable[1] == 1)
				begin
					write_address_register[15:8] <= slave_writedata[15:8];
				end
				if (slave_byteenable[2] == 1)
				begin
					write_address_register[23:16] <= slave_writedata[23:16];
				end
				if (slave_byteenable[3] == 1)
				begin
					write_address_register[31:24] <= slave_writedata[31:24];
				end		
			end
		end
	end
	
	assign control_write_address = write_address_register;
/**************************************************************/



/**************************************************************
 Length register
 **************************************************************/
	always @ (posedge clk or posedge reset)
	begin
		if (reset)
		begin
			length_register <= 0;
		end
		else
		begin
			if ((slave_address == 3'b011) & (slave_write == 1))
			begin
				if (slave_byteenable[0] == 1)
				begin
					length_register[7:0] <= slave_writedata[7:0];
				end
				if (slave_byteenable[1] == 1)
				begin
					length_register[15:8] <= slave_writedata[15:8];
				end
				if (slave_byteenable[2] == 1)
				begin
					length_register[23:16] <= slave_writedata[23:16];
				end
				if (slave_byteenable[3] == 1)
				begin
					length_register[31:24] <= slave_writedata[31:24];
				end		
			end
		end
	end
	
	assign control_read_length = length_register;
	assign control_write_length = length_register;  // same thing since this is a DMA
/**************************************************************/



/**************************************************************
 Control register
 **************************************************************/
	always @ (posedge clk or posedge reset)
	begin
		if (reset)
		begin
			control_register <= 0;
		end
		else
		begin
			if ((slave_address == 3'b110) & (slave_write == 1))
			begin
				if (slave_byteenable[0] == 1)
				begin
					control_register[7:0] <= slave_writedata[7:0];
				end
				if (slave_byteenable[1] == 1)
				begin
					control_register[15:8] <= slave_writedata[15:8];
				end
				if (slave_byteenable[2] == 1)
				begin
					control_register[23:16] <= slave_writedata[23:16];
				end
				if (slave_byteenable[3] == 1)
				begin
					control_register[31:24] <= slave_writedata[31:24];
				end		
			end
		end
	end
	
	assign control_fixed_read_address = control_register[8];  // control_register[8] is the RCON (fixed read address) bit
	assign control_fixed_write_address = control_register[9];  // control_register[9] is the WCON (fixed write address) bit
/**************************************************************/



/**************************************************************
 Go, clear, and done strobes
 **************************************************************/
	always @ (posedge clk or posedge reset)
	begin
		if (reset)
		begin
			slave_write_d1 <= 0;
			slave_address_d1 <= 0;
			slave_byteenable_d1 <= 0;
		end
		else
		begin
			slave_write_d1 <= slave_write;
			slave_address_d1 <= slave_address;
			slave_byteenable_d1 <= slave_byteenable;
		end
	end


	assign control_read_go = (slave_write_d1 == 1) & (slave_address_d1 == 3'b110) & (control_register[3] == 1) & (slave_byteenable_d1[0] == 1);  // control_register[3] is the go bit
	assign control_write_go = control_read_go;  // same thing since both 'go' at the same time
	assign control_clear = (slave_write_d1 == 1) & (slave_address_d1 == 3'b110) & (control_register[0] == 1) & (slave_byteenable_d1[0] == 1);  // control_register[0] is the clear transform bit

	always @ (posedge clk or posedge reset)
	begin
		if (reset)
			done_d1 <= 1;
		else
			done_d1 <= control_write_done;
	end
	assign done_strobe = (control_write_done == 1) & (done_d1 == 0);  // this fires right when the last write goes out the door
/**************************************************************/


endmodule
