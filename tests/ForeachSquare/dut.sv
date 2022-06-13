module dut;

    int array[16][16];

    initial begin
        foreach(array[i])
            foreach(array[i][j])
                array[i][j] = i * j;
    end

endmodule
