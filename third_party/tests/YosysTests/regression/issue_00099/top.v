module top(in, out, out1, out2, out3);
    input [7:0] in;
    output [7:0] out;
    output out1;
    output out2;
    output out3;
    parameter p = 23;
    function [7:0] test1;
        input [7:0] i;
        parameter p = 42;
        begin
            test1 = i + p;
        end
    endfunction
    function [7:0] test2;
        input [7:0] i;
        parameter p2 = p+42;
        begin
            test2 = i + p2;
        end
    endfunction
    function [7:0] test3;
        input [7:0] i;
        begin
            test3 = i + p;
        end
    endfunction
    assign out1 = test1(in);
    assign out2 = test2(in);
    assign out3 = test3(in);
endmodule
