

module lzc #(
  parameter int unsigned WIDTH = 64
) (

);

  localparam int NUM_LEVELS = $clog2(WIDTH);
  localparam int  level = 4;

  if (level == NUM_LEVELS-1) begin : g_last_level
  end else begin 
    if (1) begin : all_true 
      localparam int POWER =  2**level;
      for (genvar l = 0; l < 2**level; l++) begin : g_level
      end
    end
  end

endmodule : lzc
