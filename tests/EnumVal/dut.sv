module top;
    typedef enum logic [5:0] {
    EXC_CAUSE_IRQ_SOFTWARE_M     = {1'b1, 5'd03},
    EXC_CAUSE_IRQ_TIMER_M        = {1'b1, 5'd07},
    EXC_CAUSE_IRQ_EXTERNAL_M     = {1'b1, 5'd11},
    EXC_CAUSE_IRQ_NM             = {1'b1, 5'd31},
    EXC_CAUSE_INSN_ADDR_MISA     = {1'b0, 5'd00},
    EXC_CAUSE_INSTR_ACCESS_FAULT = {1'b0, 5'd01},
    EXC_CAUSE_ILLEGAL_INSN       = {1'b0, 5'd02},
    EXC_CAUSE_BREAKPOINT         = {1'b0, 5'd03},
    EXC_CAUSE_LOAD_ACCESS_FAULT  = {1'b0, 5'd05},
    EXC_CAUSE_STORE_ACCESS_FAULT = {1'b0, 5'd07},
    EXC_CAUSE_ECALL_UMODE        = {1'b0, 5'd08},
    EXC_CAUSE_ECALL_MMODE        = {1'b0, 5'd11}
    } exc_cause_e;
endmodule
