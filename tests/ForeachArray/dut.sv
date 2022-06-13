module dut;

    int array[16];

    initial begin
        foreach(array[i])
            array[i] = i;
    end

endmodule
