`timescale 1 ns/1 ps
module sram(CSB,WRB,ABUS,DBUS);
 
input CSB;            // active low chip select
input WRB;            // active low write control
input [11:0] ABUS;    // 12-bit address bus
inout [7:0] DBUS;     //  8-bit data bus
 
`pragma protect begin
reg  [7:0] DBUS_driver;
wire [7:0] DBUS = DBUS_driver;
reg [7:0] ram[0:4095];  // memory cells
 
integer i;
initial                 // initialize all RAM cells to 0 at startup
   begin
   DBUS_driver = 8'bzzzzzzzz;
   for (i=0; i < 4095; i = i + 1)
     ram[i] = 0;
   end
 
specify
  $setup(ABUS,posedge WRB,10);
endspecify
 
always @(CSB or WRB or ABUS)
  begin
    if (CSB == 1'b0)
      begin
      if (WRB == 1'b0) //start to sram, data will be latched in on 
                       //rising edge of CSB or WRB
        begin
        DBUS_driver <= #10 8'bzzzzzzzz;
        @(posedge CSB or posedge WRB);
        $display($time,,ABUS,DBUS);
        ram[ABUS] = DBUS;
        end
      else if (WRB == 1'b1) //reading from sram (data becomes valid after 10ns)
        begin
        #10 DBUS_driver =  ram[ABUS];
        $display($time,,ABUS,DBUS_driver);
        end
      end
    else //sram unselected, stop driving bus after 10ns
      begin
      DBUS_driver <=  #10 8'bzzzzzzzz;
      end
  end
`pragma protect end
endmodule



`timescale 1 ns/1 ps
module sram(CSB,WRB,ABUS,DBUS);
 
input CSB;                // active low chip select
input WRB;                // active low write control
input [11:0] ABUS;        // 12-bit address bus
inout [7:0] DBUS;         // 8-bit data bus
 
`pragma reset protect
endmodule
