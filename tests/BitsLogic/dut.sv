package SchedulerTypes;

typedef struct packed // IntIssueQueueEntry
{
    logic a;
} IntIssueQueueEntry;

endpackage

import SchedulerTypes::*;

module top();

 typedef struct packed {
        // Int op data
        logic [2 : 0] intValid;
        IntIssueQueueEntry [2 : 0] intData;

        // Mem op data
        logic [2 : 0] memValid;
        logic [2: 0] memAddrHit;
    } ReplayQueueEntry;

parameter p = $bits(ReplayQueueEntry);

logic [p-1:0] b;

endmodule // top
