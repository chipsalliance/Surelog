module top(i_clk,b);
input i_clk;
output b;

wire value = 0;


reg f_past_gbl_clock_valid;
initial f_past_gbl_clock_valid = 0;
always @(posedge i_clk)
  f_past_gbl_clock_valid <= 1'b1;

function automatic [19:0] zz_coreArea_uartBridge_uartConfigReg_clockDivider(input dummy);
    begin
      zz_coreArea_uartBridge_uartConfigReg_clockDivider = (20'b00000000000000000000);
      zz_coreArea_uartBridge_uartConfigReg_clockDivider = (20'b00000000000000011010);
    end
  endfunction

assign b = f_past_gbl_clock_valid;

endmodule
