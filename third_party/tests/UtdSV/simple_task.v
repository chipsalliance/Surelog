module simple_task();

task convert;
input [7:0] temp_in;
output [7:0] temp_out;
begin
  temp_out = (9/5) *( temp_in + 32);
end
endtask

endmodule
