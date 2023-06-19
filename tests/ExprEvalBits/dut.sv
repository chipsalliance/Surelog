module top(output int o);
    parameter int PARAM = 4;
    typedef enum logic[$bits(PARAM) - 32 + 85 + PARAM:0] {
        LOGIC90PB_0_ITEM_0 = 0,
        LOGIC90PB_0_ITEM_1 = 1
    } logic90pb_0_e;
    
endmodule

