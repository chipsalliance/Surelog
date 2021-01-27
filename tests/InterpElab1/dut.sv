module dut();

   localparam int unsigned TIMEOUT_CNT_W = 5;
   localparam int unsigned OP_W          = 5;

    typedef enum logic [1:0] {
      DUMMY_ADD = 2'b00,
      DUMMY_MUL = 2'b01,
      DUMMY_DIV = 2'b10,
      DUMMY_AND = 2'b11
    } dummy_instr_e;

    typedef struct packed {
      dummy_instr_e             instr_type;
      logic [OP_W-1:0]          op_b;
      logic [OP_W-1:0]          op_a;
      logic [TIMEOUT_CNT_W-1:0] cnt;
    } lfsr_data_t;
    localparam int unsigned LFSR_OUT_W = $bits(lfsr_data_t);

endmodule
