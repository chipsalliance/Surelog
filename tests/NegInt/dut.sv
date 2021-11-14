module find_first_one #( parameter int WIDTH = -1) ();
    for (genvar i = 0; i < WIDTH; i++) begin
        assign in_tmp[i] = FLIP ? in_i[WIDTH-1-i] : in_i[i];
    end
endmodule

