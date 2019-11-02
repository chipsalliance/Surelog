module testbench;
    reg en;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 en = 0;
        repeat (10000) begin
            #5 en = 1;
            #5 en = 0;
        end

        $display("OKAY");    
    end
   
    
    reg dinA;
    wire [1:0] dinB;    
    wire [1:0] dinC;

    top uut (
        .en (en ),
        .a (dinA ),
        .b (dinB ),
        .c (dinC )
    );
    
    initial begin
        dinA <= 1;
        #10
        dinA <= 0;
        #10
        dinA <= 1;
    end
    
endmodule
