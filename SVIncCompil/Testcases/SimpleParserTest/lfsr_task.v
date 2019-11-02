
module LFSR_TASK (clock, Reset, seed1, seed2, random1, random2);
input clock;
input [7:0] seed1;
output [7:0] random1, random2;
reg [7:0] random1, random2;
parameter [7:0] Chain1 = 8'b10001110;
parameter [7:0] Chain2 = 8'b10101110;
 task LFSR_TAPS8_TASK;
 input [7:0] A;
 input [7:0] Chain;
 output [7:0] Next_LFSR_Reg;
 integer i;
 reg XorNor;
 reg [7:0] Next_LFSR_Reg;
 begin
 XorNor = A[7] ^ ~| A[6:0];
 for (i=1; I<=7; i=I+1)
 if (Chain[i-1] == 1)
 Next_LFSR_Reg[i] = A[i-1] ^ XorNor;
 else
 Next_LFSR_Reg[i] = A[i-1];
 Next_LFSR_Reg[0] = XorNor;
 end
 endtask /* LFSR_TAP8_TASK */
/* Build 2 LFSRs using the LFSR_TAPS8_TASK */
always@(posedge clock or negedge Reset)
 if (!Reset)
 random1 = seed1;
 else
 LFSR_TASK (random1, Chain1, random1);
always@(posedge clock or negedge Reset)
 if (!Reset)
 random2 = seed2;
 else
 LFSR_TASK (random2, Chain2, random2);
endmodule