typedef struct packed {
    int nextAddr;   
} BranchResult;

typedef struct packed {
    BranchResult brResult;  
} IntegerRegisterWriteStageRegPath;


module IntegerRegisterWriteStage();

IntegerRegisterWriteStageRegPath pipeReg [2];

assign o = pipeReg[1].brResult.nextAddr;

endmodule
