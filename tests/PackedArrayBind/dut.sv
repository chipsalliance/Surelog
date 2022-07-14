module PreDecodeStage();

typedef logic [1:0] MSHR_IndexPath;

typedef struct packed // MemOpInfo
{
    MSHR_IndexPath mshrID;
} MemOpInfo;

typedef struct packed // MemIssueQueueEntry
{
    MemOpInfo memOpInfo;
} MemIssueQueueEntry;

typedef struct packed {
   
        MemIssueQueueEntry [1 : 0] memData;
        
    } ReplayQueueEntry;


ReplayQueueEntry replayEntryOut;

assign  mshrID = replayEntryOut.memData[0].memOpInfo.mshrID;
    
endmodule
