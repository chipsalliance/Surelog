module my_opt_reduce_or();
    parameter A_SIGNED = 0;
    parameter A_WIDTH = 1;

    parameter logic [1:0][2:0] _TECHMAP_CONSTMSK_A_ = '{0, 0};
   
    function integer count_nonconst_bits;
        integer i;
        begin
            count_nonconst_bits = 0;
            for (i = 0; i < A_WIDTH; i=i+1)
                if (!_TECHMAP_CONSTMSK_A_[i])
                    count_nonconst_bits = count_nonconst_bits+1;
        end
    endfunction
/*
    function has_const_one;
        integer i;
        begin
            has_const_one = 0;
            for (i = 0; i < A_WIDTH; i=i+1)
                if (_TECHMAP_CONSTMSK_A_[i] && _TECHMAP_CONSTVAL_A_[i] === 1'b1)
                    has_const_one = 1;
        end
    endfunction
*/
   
    reg [count_nonconst_bits()-1:0] tmp;


endmodule
