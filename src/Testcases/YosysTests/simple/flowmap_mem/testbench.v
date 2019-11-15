module testbench;
    reg clk;

    initial begin
        // $dumpfile("testbench.vcd");
        // $dumpvars(0, testbench);

        #5 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end

        $display("OKAY");    
    end
   
    
    reg [7:0] data_a = 0;
	reg [7:0] data_b = 0;
	reg [5:0] addr_a = 0;	
	reg [5:0] addr_b = 0;
    reg we_a = 0;
	reg we_b = 1;
	wire [7:0] q_a,q_b;

    top uut (
    .data_a(data_a),
	.data_b(data_b),
	.addr_a(addr_a),
	.addr_b(addr_b),
	.we_a(we_a), 
	.we_b(we_b), 
	.clk(clk),
	.q_a(q_a), 
	.q_b(q_b)
    );
    
    always @(posedge clk) begin
    #3;
    data_a <= data_a + 17;	
    data_b <= data_b + 5;
	
    addr_a <= addr_a + 1;	
    addr_b <= addr_b + 1;
    end
	
	always @(posedge clk) begin
    //#3;
    we_a <= !we_a; 
    we_b <= !we_b; 
    end
	
	uut_mem_checker port_a_test(.clk(clk), .en(!we_a), .A(q_a));
    uut_mem_checker port_b_test(.clk(clk), .en(!we_b), .A(q_b));
    
endmodule

module uut_mem_checker(input clk, input en, input [7:0] A);
    always @(posedge clk)
    begin
        #1;
        if (en == 1 & A === 8'bXXXXXXXX)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A);
            $stop;
        end
    end
endmodule
