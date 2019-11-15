
module tb_operators ;

wire [31:0] shifter;
wire [31:0] result;

initial begin
    
    $monitor(shifter,result);
    shifter = 32'b1;

    result = shifter << 4;
    result = shifter >> 4;
    result = shifter << 4;
    result = {1'b1,31'b0} >>> 31;
    result = {1'b0,31'b1} <<< 31;
    
    result = shifter ** 2;
    result = result % 4;

    if(shifter >= result) begin
        $display("GTE TEST 1");
    end else if(shifter != result) begin
        $display("GTE TEST 2");
    end else if(shifter === result) begin
        $display("GTE TEST 3");
    end else if(shifter !== result) begin
        $display("GTE TEST 3");
    end

    result  = shifter !== shifter;

    shifter = shifter ~& result;
    shifter = shifter ~| result;
end

endmodule
