

module tb_loops;
    
integer a = 0;

initial begin

    while(a < 10) begin
        a = a + 1;
    end 

    wait (10);

    forever begin
        a = a - 1;
        if( a < 0) $finish;
    end

end

endmodule
