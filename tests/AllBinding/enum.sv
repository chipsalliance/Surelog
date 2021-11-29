typedef enum logic[1:0] {
    SCR1_MEM_RESP_NOTRDY    = 2'b00,
    SCR1_MEM_RESP_RDY_OK    = 2'b01,
    SCR1_MEM_RESP_RDY_ER    = 2'b10
} type_scr1_mem_resp_e;
