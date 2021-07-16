module dut;
   typedef enum logic {c = 0, d = 1} cstate_e;

   struct packed {
      cstate_e [1:0] class_esc_state;
      logic [3:2] blah;
   } hw2reg_wrap_t;
endmodule
