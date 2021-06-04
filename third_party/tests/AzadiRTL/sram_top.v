`include "utils.vh"
module sram_top
 #(  parameter NUM_WMASKS    = 4,
     parameter MEMD = 2048,
     parameter DATA_WIDTH    = 32, // data width
     parameter nRPORTS = 1 , // number of reading ports
     parameter nWPORTS = 1, // number of write ports
     parameter IZERO   = 0 , // binary / Initial RAM with zeros (has priority over IFILE)
     parameter IFILE   = "",  // initialization mif file (don't pass extension), optional
     parameter BASIC_MODEL = 1024,
     parameter ADDR_WIDTH = 11,
     parameter DELAY = 3
  )( /*`ifdef USE_POWER_PINS
  inout vdd;
  inout gnd;
`endif*/
  input  clk, // clock
  input  csb, // active low chip select
  input  web, // active low write control
  input [NUM_WMASKS-1:0]  wmask, // write mask
  input [ADDR_WIDTH-1:0]  addr,
  input [DATA_WIDTH-1:0]  din,
  output reg[DATA_WIDTH-1:0]  dout,
  input clk1,
  input csb1,
  input [ADDR_WIDTH-1:0] addr1,
  output reg [DATA_WIDTH-1:0] dout1);

localparam ADDRW = ADDR_WIDTH; // address width
localparam NUM_OF_BANKS = MEMD / BASIC_MODEL;
localparam Basic_ADDRW = `log2(BASIC_MODEL); // address width

reg [DATA_WIDTH-1:0] RData_out;
wire[DATA_WIDTH-1:0] Rdata [NUM_OF_BANKS-1:0];
wire [(NUM_OF_BANKS-1)/2:0] Addr_sel;
reg  [(NUM_OF_BANKS-1)/2:0] Raddr_sel; 
reg [Basic_ADDRW-1:0] Addr [NUM_OF_BANKS-1:0];
reg wen [NUM_OF_BANKS-1:0];
reg csb_i [NUM_OF_BANKS-1:0];
reg web_reg;

// port  2
reg [DATA_WIDTH-1:0] RData_out_1;
wire[DATA_WIDTH-1:0] Rdata_1 [NUM_OF_BANKS-1:0];
wire [(NUM_OF_BANKS-1)/2:0] Addr_sel_1;
reg  [(NUM_OF_BANKS-1)/2:0] Raddr_sel_1;
reg [Basic_ADDRW-1:0] Addr_1 [NUM_OF_BANKS-1:0];
reg csb_i_1 [NUM_OF_BANKS-1:0];


assign Addr_sel = addr % NUM_OF_BANKS;
assign Addr_sel_1 = addr1 % NUM_OF_BANKS;

always @(negedge clk) begin
Raddr_sel = addr % NUM_OF_BANKS;
Raddr_sel_1 = addr1 % NUM_OF_BANKS;
web_reg = web;
end

integer i;
integer j;

 always @* begin
	for(i=0; i<NUM_OF_BANKS; i=i+1) begin
	Addr[i] = (Addr_sel == i) ? addr[ADDRW-1:ADDRW-Basic_ADDRW] : 0;
        wen[i] = (Addr_sel == i) ? web : 1;
	csb_i[i] = (Addr_sel == i) ? csb : 1;
	end
end

always @* begin
	for(i=0; i<NUM_OF_BANKS; i=i+1) begin
        Addr_1[i] = (Addr_sel_1 == i) ? addr1[ADDRW-1:ADDRW-Basic_ADDRW] : 0;
        csb_i_1[i] = (Addr_sel_1 == i) ? csb1 : 1;
	end
end

genvar p;
generate
	for(p=0; p<NUM_OF_BANKS; p=p+1) begin
		sram #( .NUM_WMASKS (NUM_WMASKS),
			.DATA_WIDTH (DATA_WIDTH),
			.ADDR_WIDTH (Basic_ADDRW),
			.RAM_DEPTH  (BASIC_MODEL),
			.DELAY(DELAY),
			.IZERO(IZERO),
			.IFILE(IFILE))
		sram_i( .clk0(clk),
			.csb0(csb_i[p]),
			.web0(wen[p]),
			.wmask0(wmask),
			.addr0(Addr[p]),
			.din0(din),
			.dout0(Rdata[p]),
                        .clk1(clk1),
                        .csb1(csb_i_1[p]),
                        .addr1(Addr_1[p]),
                        .dout1(Rdata_1[p]));
	end
endgenerate

always @(posedge clk) begin
        if(web_reg==1) begin
	for(j=0; j<NUM_OF_BANKS; j=j+1) begin
	 RData_out = (Raddr_sel == j) ? Rdata[j] : RData_out;
	end
        end
        else
         RData_out = RData_out;
        // Port 2
end
always @(posedge clk) begin 
        for(j=0; j<NUM_OF_BANKS; j=j+1) begin
        //RData_out_1 = (Raddr_sel_1 == q) ? Rdata_1[q] : RData_out_1;
	if(Raddr_sel_1 == j) 
        RData_out_1 = Rdata_1[j];
        else
        RData_out_1 = RData_out_1;	
	end
end



always @* begin
dout = RData_out;
end

always @* begin
dout1 = RData_out_1;
end
endmodule


