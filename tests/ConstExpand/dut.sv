module top(output int o);
   typedef struct packed {
      int operand_a;
      int unused;
   } mac_bignum_operation_t;

   mac_bignum_operation_t operation_i = '{operand_a: '1, default: '0};

   always_comb begin
      unique case (0)
         0: o = operation_i.operand_a[0+:32];
         default: o = '0;
      endcase
   end
endmodule


