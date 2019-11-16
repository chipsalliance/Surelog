module top (
input reset,
input clk,
input any_push,
input any_pop
);
reg [1:0] fifo_head [3:0];
reg [1:0] fifo_next [3:0];
wire [1:0] fifo_head4samp [3:0];
genvar fifo_num ;
integer pntr_num,fifoifo_num;

generate
for (fifo_num=0; fifo_num<4; fifo_num=fifo_num+1) begin:fifo_gen
assign fifo_head4samp[fifo_num] = fifo_next[fifo_head[fifo_num]] ; /* this is line 16 */
end
endgenerate

always @(posedge clk or negedge reset)
begin
if (!reset) begin
for (pntr_num=0; pntr_num<4; pntr_num=pntr_num+1)
fifo_next[pntr_num] <= {2{1'b0}} ;
end
else if (any_push | any_pop) begin
for (fifoifo_num=0; fifoifo_num<4; fifoifo_num=fifoifo_num+1) begin
fifo_head[fifoifo_num] <= fifo_head4samp[fifoifo_num] ;
end
end
end

endmodule
