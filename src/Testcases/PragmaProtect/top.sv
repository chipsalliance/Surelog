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
        $display($time," Writing %m ABUS=%h DATA=%h",ABUS,DBUS);
        ram[ABUS] = DBUS;
        end
      else if (WRB == 1'b1) //reading from sram (data becomes valid after 10ns)
        begin
        #10 DBUS_driver =  ram[ABUS];
        $display($time," Reading %m ABUS=%h DATA=%h",ABUS,DBUS_driver);
        end
      end
    else //sram unselected, stop driving bus after 10ns
      begin
      DBUS_driver <=  #10 8'bzzzzzzzz;
      end
  end
`pragma protect end
endmodule

`protected
module secret (a, b);
 input a;
 output b;
`pragma protect encoding=(enctype="raw")
`pragma protect data_method="x-caesar", data_keyname="rot13", begin
`pragma protect runtime_license=(library="lic.so",feature="runSecret",entry="chk", match=42)
 reg b;
 initial
 begin
 b = 0;
 end
 always
 begin
 #5 b = a;
 end
`pragma protect end
endmodule // secret
`endprotected


`timescale 1 ns/1 ps 
module sram(CSB,WRB,ABUS,DBUS);
 
input CSB;                // active low chip select
input WRB;                // active low write control
input [11:0] ABUS;        // 12-bit address bus
inout [7:0] DBUS;         // 8-bit data bus
 
`pragma protect begin_protected
`pragma protect encrypt_agent = "SynaptiCAD VeriLogger Extreme"
`pragma protect encrypt_agent_info = "13.20a"
`pragma protect data_method = "aes128-cbc"
`pragma protect key_keyowner = "SynaptiCAD" 
`pragma protect key_keyname = "syncad", key_method = "rsa"
`pragma protect key_block encoding = (enctype = "base64")
K0c+W1GDd9YcMBiX3ZqvpyTdb9sTWK06w75CLxQWVrmc3L9rzWMKgZ8vZhFcBsMT
t9K7aZTd7cJidH5kbBZbCRAZmn1xvTgmkTY7OZYtejMKStrp2bweOCxNgujIrPqo
S7Sn8oFlbG9tPn7jMCdKpyWg+20EH74G9ss7MXAJey8=
`pragma protect data_block encoding = (enctype = "base64", bytes = 1059)
Y1XAstZb24qy35cVbs13JwZp8GncAXhU4FpR2dX1rBlg0zECK0A1CNN6sPhox8ty
ZJZucCjN8EE5cbAhhw16W230HmPtWM8mQu5PwIUN/Te5Cd9CJSjIGvgJWFqJStUk
a+YBiWOT3cYXjh15krCRpeZvvqdRwvfa+yY57UeLyggomvqPScSGtmnS3S+5hQur
...
yP4QT/S4ATdx2eku9kx0Sew9EVMCA69huZN1ZIfpsKQXPMvIb/DSZnsnZhlQicCK
wqPfzxcOB1x9OK5yvgaxUf6XVvW2IFk2+kLqwL5Uc5IT/BF1fRmQQh63Bo/XA6Eu
M6sxuyIlXqvHkcZROqkyg52e/pq6yaVd0JvXkQBlaIdaa5Ebu4WkBWkPtk368KIc
2HEBVaus9ZQyGYVleOZbQA==
`pragma protect end_protected
`pragma reset protect
endmodule
