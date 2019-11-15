module testbench;
    reg clk;

    initial begin
        //$dumpfile("testbench.vcd");
        //$dumpvars(0, testbench);

        #0 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");
    end


   reg [1:0] adr = 0;
   reg [1:0] din = 0;
   wire [1:0] q;
   reg mem_init = 0;

   always @(posedge clk) begin
    #3;
    din <= din + 1;
    adr <= adr + 1;
    end

    always @(posedge adr) begin
    #10;
        if(adr == 2'b11)
            mem_init <= 1;
    end

    top uut (adr,clk,din,q);

    uut_mem_checker port_b_test(.clk(clk), .init(mem_init), .A(q));

endmodule

module uut_mem_checker(input clk, input init, input [1:0] A);
    always @(posedge clk)
    begin
        #1;
        if (init == 1 & A === 2'bXX)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A);
            $stop;
        end
    end
endmodule
