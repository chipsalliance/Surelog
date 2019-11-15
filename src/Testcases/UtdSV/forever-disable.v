
module forever_disable();

initial begin
    i = 0;
    forever begin : continue_block
        if (i==a)
            disable continue_block;
        #1 i = i + 1;
    end
end

endmodule
