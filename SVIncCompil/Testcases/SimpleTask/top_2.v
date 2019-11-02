
module bus_wr_rd_task();

`define append(f) f``_master 
`define append(f) f``_master 
`define my_macro(CK,DATA)\
   reg CK,rd,wr,ce; \
   reg [7:0]  addr,data_wr,``DATA``_rd; \
   reg [7:0]  read_``DATA``; 

   `my_macro(clk,data)
   initial begin
     clk = 0;
     read_data = 0;
   $display("Internal error: null handle at %s, line %d.",`__FILE__, `__LINE__);
    rd = 0;
    wr = 0;
    ce = 0;
    addr = 0;
    data_wr = 0;
    data_rd = 0;
    // Call the write and read tasks here
     #1  cpu_write(8'h11,8'hAA);
     #1  cpu_read(8'h11,read_data);
     #1  cpu_write(8'h12,8'hAB);
     #1  cpu_read(8'h12,read_data);
     #1  cpu_write(8'h13,8'h0A);
     #1  cpu_read(8'h13,read_data);
     #100  $finish;
  end
  // Clock Generator
  always
     #1  clk = ~clk;
  // CPU Read Task
  task cpu_read;
    input [7:0]  address;
    output [7:0] data;
    begin
      $display ("%g CPU Read  task with address : %h", $time, address);
      $display ("%g  -> Driving CE, RD and ADDRESS on to bus", $time);
      @ (posedge clk);
      addr = address;
      ce = 1;
      rd = 1;
      @ (negedge clk);
      data = data_rd;
      @ (posedge clk);
      addr = 0;
      ce = 0;
      rd = 0;
      $display ("%g CPU Read  data              : %h", $time, data);
      $display ("======================");
    end
  endtask
  // CU Write Task
  task cpu_write;
    input [7:0]  address;
    input [7:0] data;
    begin
      $display ("%g CPU Write task with address : %h Data : %h", 
        $time, address,data);
      $display ("%g  -> Driving CE, WR, WR data and ADDRESS on to bus", 
        $time);
      @ (posedge clk);
      addr = address;
      ce = 1;
      wr = 1;
      data_wr = data;
      @ (posedge clk);
      addr = 0;
      ce = 0;
      wr = 0;
      $display ("======================");
    end
  endtask
  
  // Memory model for checking tasks
  reg [7:0] mem [0:255];
  
  always @ (addr or ce or rd or wr or data_wr)
  if (ce) begin
    if (wr) begin
      mem[addr] = data_wr;
    end
    if (rd) begin
      data_rd = mem[addr];
    end
  end
  
  endmodule
