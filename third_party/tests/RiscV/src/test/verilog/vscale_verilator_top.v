`include "vscale_ctrl_constants.vh"
`include "vscale_csr_addr_map.vh"

module vscale_verilator_top(
                            input                        clk,
                            input                        reset
                            );

   localparam hexfile_words = 8192;

   wire htif_pcr_resp_valid;
   wire [`HTIF_PCR_WIDTH-1:0] htif_pcr_resp_data;

   reg [  63:0]               max_cycles;
   reg [  63:0]               trace_count;
   reg [255:0]                reason;
   reg [1023:0]               loadmem;
   integer                    stderr = 32'h80000002;

   reg [127:0]                hexfile [hexfile_words-1:0];

   wire                       htif_pcr_req_ready;
   
   vscale_sim_top DUT(
                      .clk(clk),
                      .reset(reset),
                      .htif_pcr_req_valid(1'b1),
                      .htif_pcr_req_ready(htif_pcr_req_ready),
                      .htif_pcr_req_rw(1'b0),
                      .htif_pcr_req_addr(`CSR_ADDR_TO_HOST),
                      .htif_pcr_req_data(`HTIF_PCR_WIDTH'b0),
                      .htif_pcr_resp_valid(htif_pcr_resp_valid),
                      .htif_pcr_resp_ready(1'b1),
                      .htif_pcr_resp_data(htif_pcr_resp_data)
                      );

   integer i = 0;
   integer j = 0;
   integer tmp = 0;
   
   initial begin
      loadmem = 0;
      reason = 0;
      max_cycles = 0;
      trace_count = 0;
      if ($value$plusargs("max-cycles=%d", max_cycles) && $value$plusargs("loadmem=%s", loadmem)) begin
         $readmemh(loadmem, hexfile);
         for (i = 0; i < hexfile_words; i = i + 1) begin
            for (j = 0; j < 4; j = j + 1) begin
               DUT.hasti_mem.mem[4*i+j] = hexfile[i][32*j+:32];
            end
         end
      end
   end // initial begin

   always @(posedge clk) begin
      trace_count = trace_count + 1;
      // $display("Current: %d, max: %d\n", trace_count, max_cycles);
      if (max_cycles > 0 && trace_count > max_cycles)
        reason = "timeout";

      if (!reset) begin
         if (htif_pcr_resp_valid && htif_pcr_resp_data != 0) begin
            if (htif_pcr_resp_data == 1) begin
               $finish;
            end else begin
               $sformat(reason, "tohost = %d", htif_pcr_resp_data >> 1);
            end
         end
      end


      if (reason) begin
         $fdisplay(stderr, "*** FAILED *** (%s) after %d simulation cycles", reason, trace_count);
         $finish;
      end
   end

endmodule // vscale_hex_tb

