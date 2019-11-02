module test(c);

input [9:0] c;

function integer a(input integer b);
    begin
        a = b+1;
    end
endfunction

localparam f = 5;
wire [a(f)-1:0] d;
//wire [a(f)-1:0] d1;
assign d = c[a(f)-1:0]; // wrong behavior
localparam e = a(f);
//assign d1 = c[e-1:0]; // correct behavior

endmodule
