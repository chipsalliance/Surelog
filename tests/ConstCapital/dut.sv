parameter int foo = 32'H7fFF;
parameter int foo2 = 32'Sd1;

module GOOD();
endmodule


module test;

if (foo == 32'h7fFF) begin  
        GOOD good1();
end


if (foo2 == 32'D1) begin  
        GOOD good2();
end

endmodule

