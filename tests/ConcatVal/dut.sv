module dut ();
  parameter logic [15:0][3:0] PRESENT_SBOX4 = {4'h2, 4'h1};

 function automatic logic [63:0] sbox4_64bit(logic [63:0] state_in, logic [15:0][3:0] sbox4);
  endfunction : sbox4_64bit
   
  typedef enum logic [5:0] {
    EXC_CAUSE_IRQ_SOFTWARE_M     = {1'b1, 5'd03},
    EXC_CAUSE_IRQ_TIMER_M        = {1'b1, 5'd07},
    EXC_CAUSE_ECALL_MMODE        = {1'b0, 5'd11}
  } exc_cause_e;

 
  assign data_state_sbox = sbox4_64bit(data_state_xor, PRESENT_SBOX4);
endmodule  

