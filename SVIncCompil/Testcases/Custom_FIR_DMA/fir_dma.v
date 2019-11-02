// fir_dma.v

// This file was auto-generated as part of a SOPC Builder generate operation.
// If you edit it your changes will probably be lost.

module fir_dma (
		input  wire        clk,                       //        clock.clk
		input  wire        reset,                     //             .reset
		input  wire [2:0]  slave_address,             //      control.address
		input  wire [31:0] slave_writedata,           //             .writedata
		input  wire        slave_write,               //             .write
		input  wire        slave_read,                //             .read
		input  wire [3:0]  slave_byteenable,          //             .byteenable
		output wire [31:0] slave_readdata,            //             .readdata
		output wire [31:0] read_master_address,       //  read_master.address
		output wire        read_master_read,          //             .read
		output wire [3:0]  read_master_byteenable,    //             .byteenable
		input  wire [31:0] read_master_readdata,      //             .readdata
		input  wire        read_master_readdatavalid, //             .readdatavalid
		input  wire        read_master_waitrequest,   //             .waitrequest
		output wire [31:0] write_master_address,      // write_master.address
		output wire        write_master_write,        //             .write
		output wire [3:0]  write_master_byteenable,   //             .byteenable
		output wire [31:0] write_master_writedata,    //             .writedata
		input  wire        write_master_waitrequest,  //             .waitrequest
		output wire [2:0]  write_master_burstcount,   //             .burstcount
		output wire        slave_irq                  //          irq.irq
	);

	pipelined_read_burst_write_dma #(
		.DATAWIDTH                 (32),
		.BYTEENABLEWIDTH           (4),
		.ADDRESSWIDTH              (32),
		.FIFOUSEMEMORY             (1),
		.READ_FIFODEPTH            (32),
		.READ_FIFODEPTH_LOG2       (5),
		.WRITE_FIFODEPTH           (32),
		.WRITE_FIFODEPTH_LOG2      (5),
		.WRITE_MAXBURSTCOUNT       (4),
		.WRITE_MAXBURSTCOUNT_WIDTH (3)
	) fir_dma (
		.clk                       (clk),                       //        clock.clk
		.reset                     (reset),                     //             .reset
		.slave_address             (slave_address),             //      control.address
		.slave_writedata           (slave_writedata),           //             .writedata
		.slave_write               (slave_write),               //             .write
		.slave_read                (slave_read),                //             .read
		.slave_byteenable          (slave_byteenable),          //             .byteenable
		.slave_readdata            (slave_readdata),            //             .readdata
		.read_master_address       (read_master_address),       //  read_master.address
		.read_master_read          (read_master_read),          //             .read
		.read_master_byteenable    (read_master_byteenable),    //             .byteenable
		.read_master_readdata      (read_master_readdata),      //             .readdata
		.read_master_readdatavalid (read_master_readdatavalid), //             .readdatavalid
		.read_master_waitrequest   (read_master_waitrequest),   //             .waitrequest
		.write_master_address      (write_master_address),      // write_master.address
		.write_master_write        (write_master_write),        //             .write
		.write_master_byteenable   (write_master_byteenable),   //             .byteenable
		.write_master_writedata    (write_master_writedata),    //             .writedata
		.write_master_waitrequest  (write_master_waitrequest),  //             .waitrequest
		.write_master_burstcount   (write_master_burstcount),   //             .burstcount
		.slave_irq                 (slave_irq)                  //          irq.irq
	);

endmodule
