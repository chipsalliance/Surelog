
module sub (output reg int_status);
endmodule

module dut ();
  parameter p = 1'b1;
  generate
    if (p == 1'b1) begin : blk
    end
  endgenerate
  generate
    genvar   loop_int;
    wire  [2:0]  int_status;
    for (loop_int = 0; loop_int < 2; loop_int = loop_int + 1)
    begin : gen_blk
        sub sub_i (
          .int_status(int_status[loop_int])
        );
    end
  endgenerate
endmodule
