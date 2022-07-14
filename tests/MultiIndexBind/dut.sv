module PreDecodeStage();


typedef enum logic [3:0]    // enum ALU_Code
{
    AC_ADD  = 4'b0000
} IntALU_Code;

typedef struct packed // IntMicroOpOperand
{
    IntALU_Code aluCode;
} IntMicroOpOperand;

typedef union packed    // MicroOpOperand
{
    IntMicroOpOperand     intOp;
} MicroOpOperand;

typedef struct packed // OpInfo
{
    MicroOpOperand operand;
} OpInfo;



OpInfo [1:0][1:0] microOps; 

assign o = microOps[i][1].operand.intOp.aluCode;

endmodule
