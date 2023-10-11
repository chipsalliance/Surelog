module top();

sequence seq_count_increment;
@(posedge clk) (count + 1'b1) or (count == 4'b1111);
endsequence

property p_count_increment;
@(posedge clk) not reset |-> count === seq_count_increment;
endproperty

endmodule