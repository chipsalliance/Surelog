interface io_bus_interface;
    logic write_en;
    
endinterface

module soc_tb();

    localparam NUM_PERIPHERALS = 2;

    enum logic[$clog2(NUM_PERIPHERALS) - 1:0] {
      IO_ONES
    } io_bus_source;

    io_bus_interface peripheral_io_bus[NUM_PERIPHERALS - 1:0]();

    assign peripheral_io_bus[IO_ONES].write_en = 32'hffffffff;

    genvar io_idx;
    generate
        for (io_idx = 0; io_idx <  NUM_PERIPHERALS; io_idx++)
        begin : io_gen
            assign peripheral_io_bus[io_idx].write_en = 1;
        end
    endgenerate

endmodule

