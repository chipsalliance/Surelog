module top();

   parameter bht_row_width_p = 10;
   
    for (genvar i = 0; i < bht_row_width_p; i+=2)
    begin : wval
      assign w_data_li[i]   = is_clear ? bht_init_lp[0] : ~correct_i;
      assign w_data_li[i+1] = is_clear ? bht_init_lp[1] : val_i[i+1] ^ (~correct_i & val_i[i]);
    end
 
endmodule

