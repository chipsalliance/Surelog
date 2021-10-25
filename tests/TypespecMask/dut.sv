module flash_ctrl_erase;
 
  localparam logic[17:0] BankAddrMask = ~(15);

  parameter int NMioPads = 8;
  parameter logic [NMioPads - 1:0] ConnectDioIn = 8'b11110000;

endmodule

