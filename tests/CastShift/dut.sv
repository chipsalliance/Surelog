module dut();
parameter logic [1:0]  CSR_MISA_MXL = 2'd1;
parameter bit RV32M        = 1;
parameter bit RV32E        = 0;
localparam logic [31:0] MISA_VALUE = 
  (0                 <<  0)  
| (1                 <<  2)  
| (0                 <<  3)  
| (32'(RV32E)        <<  4) 
| (0                 <<  5)  
| (32'(!RV32E)       <<  8)  
| (32'(RV32M)        << 12)  
| (0                 << 13)  
| (0                 << 18)  
| (1                 << 20)  
| (0                 << 23)  
| (32'(CSR_MISA_MXL) << 30); 

if (MISA_VALUE == 1074794756) begin
  OK ok();
end

endmodule

