// povik/sv-elab#308 / #289: static methods of a PARAMETERIZED class called
// as `rotate #(N)::calc(x)`.  Surelog compiled the call to a bare ref_obj
// `rotate::calc` (arguments dropped) and read_uhdm warned "Reference to
// unknown signal" and drove X.  The 8- and 16-bit specializations must each
// rotate left by one at their own width.
class rotate #(parameter int unsigned DATA_WIDTH = 8);
    static function logic [DATA_WIDTH-1:0] calc(logic [DATA_WIDTH-1:0] data);
        calc = {data[DATA_WIDTH-2:0], data[DATA_WIDTH-1]};
    endfunction
endclass

module top(input logic [7:0] in1, input logic [15:0] in2,
           output logic [7:0] out1, output logic [15:0] out2);
    assign out1 = rotate #(8)::calc(in1);
    assign out2 = rotate #(16)::calc(in2);
endmodule
