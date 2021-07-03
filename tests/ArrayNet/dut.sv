module  memory();
reg [7:0] my_memory [0:255];

initial begin
 $readmemh("memory.list", my_memory);
end
endmodule
