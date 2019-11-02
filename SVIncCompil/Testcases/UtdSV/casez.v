

module tb_casez;

wire [31:0] shifter;
wire [31:0] result;

initial begin
    
    $monitor(shifter,result);
    shifter = 32'b1;

    result = shifter << 4;

    casez(result)
        32'b10000 : $display("true");
        32'b11000 : $display("false");
    endcase
    
    casez(result)
        32'b11000 : $display("false");
        default: $display("default case");
    endcase

end

endmodule
