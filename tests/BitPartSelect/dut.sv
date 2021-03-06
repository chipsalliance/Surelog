module top();
   parameter int unsigned Width       = 16;
   parameter int unsigned Depth      = 4;
   localparam int unsigned PTR_WIDTH = 2;
   logic [Depth-1:0][Width-1:0] storage;
   logic [Width-1:0] storage_rdata;
  logic [PTR_WIDTH-1:0] fifo_rptr;

   assign storage_rdata = storage[fifo_rptr[PTR_WIDTH-2:0]];
endmodule // top

