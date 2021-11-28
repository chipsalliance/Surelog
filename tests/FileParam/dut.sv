localparam P1 = 1;

localparam P2 = P1 + 2;

typedef enum int unsigned {
    SCR1_SCU_DR_SYSCTRL_OP_BIT_R                  = 'h0,
    SCR1_SCU_DR_SYSCTRL_OP_BIT_L                  = P2+4
    
} type_scr1_scu_sysctrl_dr_bits_e;


module top();
endmodule
