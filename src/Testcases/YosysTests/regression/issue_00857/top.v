module top(data_in,data_out,clk);
output reg data_out;
input data_in;
input clk;

always @(posedge clk)
begin
myTask(data_out,data_in);
end
task myTask;
output out;
input in;
out = in;
endtask
endmodule
