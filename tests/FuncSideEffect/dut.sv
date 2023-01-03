module const_fold_func_top(
    input wire [3:0] inp,
    output wire [3:0] out1,
    output reg [3:0] out2
);

    function automatic [3:0] flip;
        input [3:0] inp;
        flip = ~inp;
    endfunction

  function automatic [3:0] pow_flip_b;
    input [3:0] base, exp;
    begin
        out2[exp] = base & 1;
        pow_flip_b = 1;
        if (exp > 0)
            pow_flip_b = base * pow_flip_b(flip(base), exp - 1); 
    end 
  endfunction

    assign out1 = pow_flip_b(2, 2); 
endmodule // const_fold_func_top
