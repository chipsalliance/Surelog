
module bc #(
            parameter SIZE=2,
            parameter WIDTH=16
            )
   (
    input                        clk,
    input                        rst,

    output wire                  din_ready,
    input wire                   din_valid,
    input wire [WIDTH-1:0]       din_data,

    input wire [SIZE-1:0]        dout_ready,
    output wire [SIZE-1:0]       dout_valid,
    output wire [WIDTH*SIZE-1:0] dout_data
    );

   reg [SIZE-1 : 0] ready_reg;
   wire [SIZE-1 : 0] ready_all;
   genvar           i;

   initial begin
      ready_reg = 0;
   end

   generate
      for (i = 0; i < SIZE; i=i+1) begin
         assign ready_all[i]  = dout_ready[i] | ready_reg[i];
         assign dout_valid[i] = din_valid & !ready_reg[i];
         assign dout_data[(i+1)*WIDTH-1:i*WIDTH]   = din_data;

         always @(posedge clk) begin
            if (rst || (!din_valid) || din_ready) begin
               ready_reg[i] <= 1'b0;
            end else if (dout_ready[i]) begin
               ready_reg[i] <= 1'b1;
            end
         end
      end
   endgenerate
   assign din_ready = &ready_all;

endmodule
