module top();
logic        first_condition, first_condition_false;
logic [31:0] first_condition_true,second_condition_true, second_condition_false, result;
assign result = first_condition       ? first_condition_true :
                first_condition_false ? second_condition_true :
                                        second_condition_false;
endmodule
