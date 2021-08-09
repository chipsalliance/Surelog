module GOOD();
endmodule

module axi();

    parameter N_MASTER        = 8;
    parameter LOG_MASTER      = $clog2(N_MASTER);
    localparam TOTAL_N_MASTER   =  2**LOG_MASTER;

      generate


      if(N_MASTER != TOTAL_N_MASTER) // Not power of 2 inputs
      begin : ARRAY_INT
      end
      else
      begin
        GOOD good();
      end
      endgenerate

endmodule
