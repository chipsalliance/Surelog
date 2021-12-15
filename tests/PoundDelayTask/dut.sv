module m;
    task t;
        $display("I'm task t!");
    endtask

    initial begin
        #1 t;
    end
endmodule
