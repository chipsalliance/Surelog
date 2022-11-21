module func_width_scope_top(inp, out1, out2);
    input wire inp;

    localparam WIDTH_A = 5;
    function automatic [WIDTH_A-1:0] func1;
        input reg [WIDTH_A-1:0] s;
        func1 = ~s; 
    endfunction
    wire [func1(0)-1:0] xc;
    assign xc = 1'sb1;

    output wire [1023:0] out1, out2;
    wire [WIDTH_A-1:0] xn; 
    assign xn = func1(inp);
    assign out1 = xn; 
    assign out2 = xc; 

endmodule // func_width_scope_top
