/*
:name: xor_assignment
:description: ^= assignment test
:tags: 11.4.1
*/
module top();

int a = 12;
int b = 5;

initial begin
    a ^= b;
end

endmodule
