module test();

parameter [1:0] foo = {1'd0, 1'b1};

if (foo == 2'b01) begin
    bar mybar();
end

endmodule // test
