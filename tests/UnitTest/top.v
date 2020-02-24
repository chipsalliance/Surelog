

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

module top (input i, output o);
wire i;
reg o;
assign o = i;
endmodule


interface mem_if (input wire clk);

  modport  system (input clk);
  modport  memory (output clk);
 
endinterface

class DD2;
endclass

module memory_ctrl1 (mem_if sif1, mem_if.system sif2);

DD1 toto1;

DD2 toto2;

wire i1;

reg o1;

endmodule

