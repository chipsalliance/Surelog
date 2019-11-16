`define CLK_RESET_FIXTURE(CLK_HPERIOD,RST_PERIOD) \
parameter clkHPeriod = CLK_HPERIOD; \
logic clk; \
logic rst_n; \
initial begin \
  clk = 1; \
  rst_n = 1; \
end \
task automatic step(int size = 1); \
  repeat (size) begin \
    int step_size = clkHPeriod - $time % (clkHPeriod); \
    #(step_size) clk <= ~clk; \
    #(clkHPeriod) clk <= ~clk; \
  end \
endtask \
task nextSamplePoint(); \
  if ($time%(clkHPeriod) == 0) #1; \
  else repeat (2) #0; \
endtask \
task reset(); \
  rst_n = 0; \
  step(RST_PERIOD); \
  rst_n = 1; \
  step(1); \
endtask \
task pause(); \
  #0; \
endtask
