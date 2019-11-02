`define CSR_ADDR_WIDTH     12
`define CSR_COUNTER_WIDTH  64

`define CSR_ADDR_CYCLE     12'hC00
`define CSR_ADDR_TIME      12'hC01
`define CSR_ADDR_INSTRET   12'hC02
`define CSR_ADDR_CYCLEH    12'hC80
`define CSR_ADDR_TIMEH     12'hC81
`define CSR_ADDR_INSTRETH  12'hC82
`define CSR_ADDR_MCPUID    12'hF00
`define CSR_ADDR_MIMPID    12'hF01
`define CSR_ADDR_MHARTID   12'hF10
`define CSR_ADDR_MSTATUS   12'h300
`define CSR_ADDR_MTVEC     12'h301
`define CSR_ADDR_MTDELEG   12'h302
`define CSR_ADDR_MIE       12'h304
`define CSR_ADDR_MTIMECMP  12'h321
`define CSR_ADDR_MTIME     12'h701
`define CSR_ADDR_MTIMEH    12'h741
`define CSR_ADDR_MSCRATCH  12'h340
`define CSR_ADDR_MEPC      12'h341
`define CSR_ADDR_MCAUSE    12'h342
`define CSR_ADDR_MBADADDR  12'h343
`define CSR_ADDR_MIP       12'h344
`define CSR_ADDR_CYCLEW    12'h900
`define CSR_ADDR_TIMEW     12'h901
`define CSR_ADDR_INSTRETW  12'h902
`define CSR_ADDR_CYCLEHW   12'h980
`define CSR_ADDR_TIMEHW    12'h981
`define CSR_ADDR_INSTRETHW 12'h982

`define CSR_ADDR_TO_HOST   12'h780
`define CSR_ADDR_FROM_HOST 12'h781

`define CSR_CMD_WIDTH 3
`define CSR_IDLE      0
`define CSR_READ      4
`define CSR_WRITE     5
`define CSR_SET       6
`define CSR_CLEAR     7

`define ECODE_WIDTH                      4
`define ECODE_INST_ADDR_MISALIGNED       0
`define ECODE_INST_ADDR_FAULT            1
`define ECODE_ILLEGAL_INST               2
`define ECODE_BREAKPOINT                 3
`define ECODE_LOAD_ADDR_MISALIGNED       4
`define ECODE_LOAD_ACCESS_FAULT          5
`define ECODE_STORE_AMO_ADDR_MISALIGNED  6
`define ECODE_STORE_AMO_ACCESS_FAULT     7
`define ECODE_ECALL_FROM_U               8
`define ECODE_ECALL_FROM_S               9
`define ECODE_ECALL_FROM_H              10
`define ECODE_ECALL_FROM_M              11

`define ICODE_SOFTWARE 0
`define ICODE_TIMER    1

`define PRV_WIDTH     2
`define PRV_U         0
`define PRV_S         1
`define PRV_H         2
`define PRV_M         3
