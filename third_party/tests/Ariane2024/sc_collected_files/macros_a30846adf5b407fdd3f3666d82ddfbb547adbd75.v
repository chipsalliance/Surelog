module SyncSpRamBeNx64_00000008_00000100_0_2
  (
   Clk_CI,
   Rst_RBI,
   CSel_SI,
   WrEn_SI,
   BEn_SI,
   WrData_DI,
   Addr_DI,
   RdData_DO
   );
   
   input [7:0]   BEn_SI; // byte-enable: ignore or use as needed
   input [63:0]  WrData_DI;
   input [7:0] 	 Addr_DI;
   output [63:0] RdData_DO;
   input 	 Clk_CI;
   input 	 Rst_RBI; // reset: ignore or use as needed
   input 	 CSel_SI;
   input 	 WrEn_SI;

  la_spram #(.DW(64), .AW(8)) macro_mem(
    .clk(Clk_CI),
    .ce(CSel_SI),
    .we(WrEn_SI),
    .wmask({64{1'b1}}),
    .addr(Addr_DI),
    .din(WrData_DI),
    .dout(RdData_DO)
  );
endmodule // SyncSpRamBeNx64_00000008_00000100_0_2

// The valid_dirty_sram should be 4 macros, each 256x16. Instead, they only instantiated 1 256x16 macro
module limping_SyncSpRamBeNx64_00000008_00000100_0_2
  (
   Clk_CI,
   Rst_RBI,
   CSel_SI,
   WrEn_SI,
   BEn_SI,
   WrData_DI,
   Addr_DI,
   RdData_DO
   );
   
   input [7:0]   BEn_SI; // byte-enable: ignore or use as needed
   input [63:0]  WrData_DI;
   input [7:0] 	 Addr_DI;
   output [63:0] RdData_DO;
   input 	 Clk_CI;
   input 	 Rst_RBI; // reset: ignore or use as needed
   input 	 CSel_SI;
   input 	 WrEn_SI;
   wire [63:0] 	 RdData_DO;
   wire 	 csel_b,wren_b;
   wire [15:0] WMaskIn, NotWMaskIn;

  la_spram #(.DW(16), .AW(8)) macro_mem(
    .clk(Clk_CI),
    .ce(CSel_SI),
    .we(WrEn_SI),
    .wmask({16{1'b1}}),
    .addr(Addr_DI),
    .din(WrData_DI[15:0]),
    .dout(RdData_DO[15:0])
  );

   assign RdData_DO[63:16] = 48'h0;

endmodule // limping_SyncSpRamBeNx64_00000008_00000100_0_2

module SyncSpRamBeNx64_00000008_00000100_0_2_d45
  (
   Clk_CI,
   Rst_RBI,
   CSel_SI,
   WrEn_SI,
   BEn_SI,
   WrData_DI,
   Addr_DI,
   RdData_DO
   );
   
   input [7:0]   BEn_SI; // byte-enable: ignore or use as needed
   input [44:0]  WrData_DI;
   input [7:0] 	 Addr_DI;
   output [44:0] RdData_DO;
   input 	 Clk_CI;
   input 	 Rst_RBI; // reset: ignore or use as needed
   input 	 CSel_SI;
   input 	 WrEn_SI;
   wire [47:0] 	 RdData_DO_wire;
   wire 	 csel_b,wren_b;
   wire [15:0] WMaskIn, NotWMaskIn;
   
  la_spram #(.DW(45), .AW(8)) macro_mem(
    .clk(Clk_CI),
    .ce(CSel_SI),
    .we(WrEn_SI),
    .wmask({45{1'b1}}),
    .addr(Addr_DI),
    .din(WrData_DI),
    .dout(RdData_DO)
  );

endmodule // SyncSpRamBeNx64_00000008_00000100_0_2_d45

module SyncSpRamBeNx64_00000008_00000100_0_2_d44
  (
   Clk_CI,
   Rst_RBI,
   CSel_SI,
   WrEn_SI,
   BEn_SI,
   WrData_DI,
   Addr_DI,
   RdData_DO
   );
   
   input [7:0]   BEn_SI; // byte-enable: ignore or use as needed
   input [43:0]  WrData_DI;
   input [7:0] 	 Addr_DI;
   output [43:0] RdData_DO;
   input 	 Clk_CI;
   input 	 Rst_RBI; // reset: ignore or use as needed
   input 	 CSel_SI;
   input 	 WrEn_SI;
   wire [47:0] 	 RdData_DO_wire;
   wire 	 csel_b,wren_b;
   wire [15:0] WMaskIn, NotWMaskIn;

  la_spram #(.DW(44), .AW(8)) macro_mem(
    .clk(Clk_CI),
    .ce(CSel_SI),
    .we(WrEn_SI),
    .wmask({44{1'b1}}),
    .addr(Addr_DI),
    .din(WrData_DI),
    .dout(RdData_DO)
  );

endmodule // SyncSpRamBeNx64_00000008_00000100_0_2_d44
