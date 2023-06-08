
module top(output logic a, output logic b);
  typedef enum logic {c = 0, d = 1} cstate_e;

   typedef struct packed {
      cstate_e [1:0] class_esc_state;
   } hw2reg_wrap_t;

   hw2reg_wrap_t hw2reg_wrap = { c, d };

   assign { a,
            b } = hw2reg_wrap.class_esc_state;

endmodule
