module top();
interconnect [0:3] [0:1] aBus;
logic [0:3] dBus;

driver driverArray[0:3](aBus);

cmp cmpArray[0:3](aBus,rst,dBus);

endmodule : top
