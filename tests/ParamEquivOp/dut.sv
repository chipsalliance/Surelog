
module GOOD();
endmodule


module top();

parameter p_edma_irq_read_clear     = 1'b0;
parameter p_edma_tx_pkt_buffer      = 1'b1;
parameter p_edma_rx_pkt_buffer      = 1'b1;
parameter p_edma_queues             = 32'd1;
parameter p_edma_tsu                = 1'b1;
parameter p_edma_axi                = 1'b1;
parameter p_edma_has_pcs            = 1'b1;
parameter p_edma_ext_fifo_interface = 1'b0;
parameter p_has_dma                 = (p_edma_ext_fifo_interface == 1'b0);

// Define interrupt bits which actually exists
parameter p_int_exists  = {
                            2'b11,                    // 31:30
                            (p_edma_tsu == 1),        // 29
                            2'b11,                    // 28:27
                            (p_edma_tsu == 1),        // 26
                            8'b11111111,              // 25:18
                            (p_edma_has_pcs == 1),    // 17
                            (p_edma_has_pcs == 1),    // 16
                            4'b1111,                  // 15:12
                            (p_has_dma == 1),         // 11
                            1'b1,                     // 10
                            (p_edma_has_pcs == 0),    // 9
                            1'b0,                     // 8 Reserved
                            1'b1,                     // 7
                            (p_has_dma == 1),         // 6
                            2'b11,                    // 5:4
                            (p_has_dma == 1),         // 3
                            (p_has_dma == 1),         // 2
                            2'b11 // 1:0
                          };

if (p_int_exists == 32'b11111111111111111111110011111111) begin
  GOOD good();
end

endmodule