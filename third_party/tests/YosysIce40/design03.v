
// Benchmark source:
// https://github.com/daveshah1/up5k-demos/tree/master/nes

// ===================================================================

module up_spram (
	input clk,
	input [3:0] wen,
	input [21:0] addr,
	input [31:0] wdata,
	output [31:0] rdata
);

wire cs_0, cs_1;
wire [31:0] rdata_0, rdata_1;

assign cs_0 = !addr[14];
assign cs_1 = addr[14];
assign rdata = addr[14] ? rdata_1 : rdata_0;


SB_SPRAM256KA ram00
  (
    .ADDRESS(addr[13:0]),
    .DATAIN(wdata[15:0]),
    .MASKWREN({wen[1], wen[1], wen[0], wen[0]}),
    .WREN(wen[1]|wen[0]),
    .CHIPSELECT(cs_0),
    .CLOCK(clk),
    .STANDBY(1'b0),
    .SLEEP(1'b0),
    .POWEROFF(1'b1),
    .DATAOUT(rdata_0[15:0])
  );

SB_SPRAM256KA ram01
  (
    .ADDRESS(addr[13:0]),
    .DATAIN(wdata[31:16]),
    .MASKWREN({wen[3], wen[3], wen[2], wen[2]}),
    .WREN(wen[3]|wen[2]),
    .CHIPSELECT(cs_0),
    .CLOCK(clk),
    .STANDBY(1'b0),
    .SLEEP(1'b0),
    .POWEROFF(1'b1),
    .DATAOUT(rdata_0[31:16])
  );

  
SB_SPRAM256KA ram10
  (
    .ADDRESS(addr[13:0]),
    .DATAIN(wdata[15:0]),
    .MASKWREN({wen[1], wen[1], wen[0], wen[0]}),
    .WREN(wen[1]|wen[0]),
    .CHIPSELECT(cs_1),
    .CLOCK(clk),
    .STANDBY(1'b0),
    .SLEEP(1'b0),
    .POWEROFF(1'b1),
    .DATAOUT(rdata_1[15:0])
  );

SB_SPRAM256KA ram11
  (
    .ADDRESS(addr[13:0]),
    .DATAIN(wdata[31:16]),
    .MASKWREN({wen[3], wen[3], wen[2], wen[2]}),
    .WREN(wen[3]|wen[2]),
    .CHIPSELECT(cs_1),
    .CLOCK(clk),
    .STANDBY(1'b0),
    .SLEEP(1'b0),
    .POWEROFF(1'b1),
    .DATAOUT(rdata_1[31:16])
  );

endmodule
module scan_double(input clk,
            input [14:0] inputpixel,
            input reset_frame,
            input reset_line,
            input [9:0] read_x,
            output reg [14:0] outpixel);
reg [1:0] frac;
reg [14:0] linebuf[0:255];
reg [8:0] write_x;

always @(posedge clk)
begin
  if(reset_line)
  begin
    frac <= 2'b00;
    write_x <= 9'd0;
  end else begin
    frac <= frac + 1;
    if (frac == 2)
      if (write_x < 256)
        write_x <= write_x + 1;
  end
end

wire write_en = ((frac == 2) && (write_x < 256)) ? 1'b1 : 1'b0;

always @(posedge clk)
begin
  outpixel <= linebuf[read_x[8:1]];
  if(write_en)
    linebuf[write_x[7:0]] <= inputpixel;
end



endmodule/**
 * PLL configuration
 *
 * This Verilog module was generated automatically
 * using the icepll tool from the IceStorm project.
 * Use at your own risk.
 *
 * Given input frequency:        16.000 MHz
 * Requested output frequency:   21.477 MHz
 * Achieved output frequency:    21.500 MHz
 */

module pll(
	input  clock_in,
	output clock_out,
	output locked
	);

SB_PLL40_CORE #(
		.FEEDBACK_PATH("SIMPLE"),
		.DIVR(4'b0000),		// DIVR =  0
		.DIVF(7'b0101010),	// DIVF = 42
		.DIVQ(3'b101),		// DIVQ =  5
		.FILTER_RANGE(3'b001)	// FILTER_RANGE = 1
	) uut (
		.LOCK(locked),
		.RESETB(1'b1),
		.BYPASS(1'b0),
		.REFERENCECLK(clock_in),
		.PLLOUTCORE(clock_out)
		);

endmodule
/*
This memory device contains both system memory
and cartridge data.
*/

module main_mem(
  input clock, reset,
  
  input reload,
  input [3:0] index,
  
  output load_done,
  output [31:0] flags_out,
  //NES interface
  input [21:0] mem_addr,
  input mem_rd_cpu, mem_rd_ppu,
  input mem_wr,
  output reg [7:0] mem_q_cpu, mem_q_ppu,
  input [7:0] mem_d,
  
  //Flash load interface
  output flash_csn,
  output flash_sck,
  output flash_mosi,
  input flash_miso);
  
// Compress the 4MB logical address space to our limited available space
// In the future a more sophisticated memory system will keep games in
// SQI flash to expand the space available

// Also may consider changing this based on mapper to make the most
// of limited memory

wire prgrom_en, chrrom_en, vram_en, cpuram_en, cartram_en;

// Mapping
// 0... : PRG       : lower 64kB SPRAM
// 10.. : CHR       : upper 64kB SPRAM
// 1100 : CHR-VRAM  : dedicated 2kB RAM
// 1110 : CPU-RAM   : dedicated 2kB RAM
// 1111 : CART-RAM  : dedicated 2kB RAM

assign prgrom_en    = !mem_addr[21];
assign chrrom_en    = mem_addr[21] & !mem_addr[20];
assign vram_en      = mem_addr[21] & mem_addr[20] & !mem_addr[19] & !mem_addr[18];
assign cpuram_en    = mem_addr[21] & mem_addr[20] & mem_addr[19] & !mem_addr[18];
assign cartram_en   = mem_addr[21] & mem_addr[20] & mem_addr[19] & mem_addr[18];

wire [20:0] segment_addr = prgrom_en ? mem_addr[20:0] : (chrrom_en ? {1'b0, mem_addr[19:0]} : {3'b0, mem_addr[17:0]});

wire [7:0] cpuram_read_data, vram_read_data, cart_read_data;
wire rden = mem_rd_cpu | mem_rd_ppu;

always@(posedge clock or posedge reset)
begin
  if (reset == 1'b1) begin
    mem_q_cpu <= 0;
    mem_q_ppu <= 0;
  end else begin
    if (mem_rd_cpu)
      mem_q_cpu <= cpuram_en ? cpuram_read_data : (vram_en ? vram_read_data : cart_read_data);
    if (mem_rd_ppu)
      mem_q_ppu <= cpuram_en ? cpuram_read_data : (vram_en ? vram_read_data : cart_read_data);
  end;
end

cart_mem cart_i (
  .clock(clock),
  .reset(reset),
  .reload(reload),
  .index(index),
  .cart_ready(load_done),
  .flags_out(flags_out),
  .address(segment_addr),
  .prg_sel(prgrom_en),
  .chr_sel(chrrom_en),
  .ram_sel(cartram_en),
  .rden(rden),
  .wren(mem_wr),
  .write_data(mem_d),
  .read_data(cart_read_data),
  
  //Flash load interface
  .flash_csn(flash_csn),
  .flash_sck(flash_sck),
  .flash_mosi(flash_mosi),
  .flash_miso(flash_miso)
);

generic_ram #(
  .WIDTH(8),
  .WORDS(2048)
) cpuram_i (
  .clock(clock),
  .reset(reset),
  .address(segment_addr[10:0]), 
  .wren(mem_wr&cpuram_en), 
  .write_data(mem_d), 
  .read_data(cpuram_read_data)
);

generic_ram #(
  .WIDTH(8),
  .WORDS(2048)
) vram_i (
  .clock(clock),
  .reset(reset),
  .address(segment_addr[10:0]), 
  .wren(mem_wr&vram_en), 
  .write_data(mem_d), 
  .read_data(vram_read_data)
);

endmodule// Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.

// Module handles updating the loopy scroll register
module LoopyGen (
					 input clk, input ce,
                input is_rendering,
                input [2:0] ain,   // input address from CPU
                input [7:0] din,   // data input
                input read,        // read
                input write,       // write
                input is_pre_render, // Is this the pre-render scanline
                input [8:0] cycle,
                output [14:0] loopy,
                output [2:0] fine_x_scroll);  // Current loopy value
  // Controls how much to increment on each write
  reg ppu_incr; // 0 = 1, 1 = 32
  // Current VRAM address
  reg [14:0] loopy_v;
  // Temporary VRAM address
  reg [14:0] loopy_t;
  // Fine X scroll (3 bits)
  reg [2:0] loopy_x;
  // Latch
  reg ppu_address_latch;
  initial begin
    ppu_incr = 0;
    loopy_v = 0;
    loopy_t = 0;
    loopy_x = 0;
    ppu_address_latch = 0;  
  end
  // Handle updating loopy_t and loopy_v
  always @(posedge clk) if (ce) begin
    if (is_rendering) begin
      // Increment course X scroll right after attribute table byte was fetched.
      if (cycle[2:0] == 3 && (cycle < 256 || cycle >= 320 && cycle < 336)) begin
        loopy_v[4:0] <= loopy_v[4:0] + 1;
        loopy_v[10] <= loopy_v[10] ^ (loopy_v[4:0] == 31);
      end

      // Vertical Increment  
      if (cycle == 251) begin
        loopy_v[14:12] <= loopy_v[14:12] + 1;
        if (loopy_v[14:12] == 7) begin
          if (loopy_v[9:5] == 29) begin
            loopy_v[9:5] <= 0;
            loopy_v[11] <= !loopy_v[11];
          end else begin
            loopy_v[9:5] <= loopy_v[9:5] + 1;
          end
        end
      end
      
      // Horizontal Reset at cycle 257
      if (cycle == 256)
        {loopy_v[10], loopy_v[4:0]} <= {loopy_t[10], loopy_t[4:0]};
  
      // On cycle 256 of each scanline, copy horizontal bits from loopy_t into loopy_v
      // On cycle 304 of the pre-render scanline, copy loopy_t into loopy_v
      if (cycle == 304 && is_pre_render) begin
        loopy_v <= loopy_t;
      end
    end
    if (write && ain == 0) begin
      loopy_t[10] <= din[0];
      loopy_t[11] <= din[1];
      ppu_incr <= din[2];
    end else if (write && ain == 5) begin
      if (!ppu_address_latch) begin
        loopy_t[4:0] <= din[7:3];
        loopy_x <= din[2:0];
      end else begin
        loopy_t[9:5] <= din[7:3];
        loopy_t[14:12] <= din[2:0];
      end
      ppu_address_latch <= !ppu_address_latch;
    end else if (write && ain == 6) begin
      if (!ppu_address_latch) begin
        loopy_t[13:8] <= din[5:0];
        loopy_t[14] <= 0;
      end else begin
        loopy_t[7:0] <= din;
        loopy_v <= {loopy_t[14:8], din};
      end
      ppu_address_latch <= !ppu_address_latch;
    end else if (read && ain == 2) begin
      ppu_address_latch <= 0; //Reset PPU address latch
    end else if ((read || write) && ain == 7 && !is_rendering) begin
      // Increment address every time we accessed a reg
      loopy_v <= loopy_v + (ppu_incr ? 32 : 1);
    end
  end
  assign loopy = loopy_v;
  assign fine_x_scroll = loopy_x;
endmodule
  
  
// Generates the current scanline / cycle counters
module ClockGen(input clk, input ce, input reset,
                input is_rendering,
                output reg [8:0] scanline,
                output reg [8:0] cycle,
                output reg is_in_vblank,
                output end_of_line,
                output at_last_cycle_group,
                output exiting_vblank,
                output entering_vblank,
                output reg is_pre_render);
  reg second_frame;
  
  // Scanline 0..239 = picture scan lines
  // Scanline 240 = dummy scan line
  // Scanline 241..260 = VBLANK
  // Scanline -1 = Pre render scanline (Fetches objects for next line)
  assign at_last_cycle_group = (cycle[8:3] == 42);
  // Every second pre-render frame is only 340 cycles instead of 341.
  assign end_of_line = at_last_cycle_group && cycle[3:0] == (is_pre_render && second_frame && is_rendering ? 3 : 4);
  // Set the clock right before vblank begins
  assign entering_vblank = end_of_line && scanline == 240;
  // Set the clock right before vblank ends
  assign exiting_vblank = end_of_line && scanline == 260;
  // New value for is_in_vblank flag
  wire new_is_in_vblank = entering_vblank ? 1'b1 : exiting_vblank ? 1'b0 : is_in_vblank;
  // Set if the current line is line 0..239
  always @(posedge clk) if (reset) begin
    cycle <= 0;
    is_in_vblank <= 1;
  end else if (ce) begin
    cycle <= end_of_line ? 0 : cycle + 1;
    is_in_vblank <= new_is_in_vblank;
  end
//  always @(posedge clk) if (ce) begin
//    $write("%x %x %x %x %x\n", new_is_in_vblank, entering_vblank, exiting_vblank, is_in_vblank, entering_vblank ? 1'b1 : exiting_vblank ? 1'b0 : is_in_vblank);
    
//  end
  always @(posedge clk) if (reset) begin
    scanline <= 0;
    is_pre_render <= 0;
    second_frame <= 0;
  end else if (ce && end_of_line) begin
    // Once the scanline counter reaches end of 260, it gets reset to -1.
    scanline <= exiting_vblank ? 9'b111111111 : scanline + 1;
    // The pre render flag is set while we're on scanline -1.
    is_pre_render <= exiting_vblank;
    
    if (exiting_vblank)
      second_frame <= !second_frame;
  end
  
endmodule // ClockGen

// 8 of these exist, they are used to output sprites.
module Sprite(input clk, input ce,
              input enable,
              input [3:0] load, 
              input [26:0] load_in,
              output [26:0] load_out,
              output [4:0] bits); // Low 4 bits = pixel, high bit = prio
  reg [1:0] upper_color; // Upper 2 bits of color
  reg [7:0] x_coord;     // X coordinate where we want things
  reg [7:0] pix1, pix2;  // Shift registers, output when x_coord == 0
  reg aprio;             // Current prio
  wire active = (x_coord == 0);
  always @(posedge clk) if (ce) begin
    if (enable) begin
      if (!active) begin
        // Decrease until x_coord is zero.
        x_coord <= x_coord - 8'h01;
      end else begin
        pix1 <= pix1 >> 1;
        pix2 <= pix2 >> 1;
      end
    end
    if (load[3]) pix1 <= load_in[26:19];
    if (load[2]) pix2 <= load_in[18:11];
    if (load[1]) x_coord <= load_in[10:3];
    if (load[0]) {upper_color, aprio} <= load_in[2:0];
  end
  assign bits = {aprio, upper_color, active && pix2[0], active && pix1[0]};
  assign load_out = {pix1, pix2, x_coord, upper_color, aprio};
endmodule  // SpriteGen
					
// This contains all 8 sprites. Will return the pixel value of the highest prioritized sprite.
// When load is set, and clocked, load_in is loaded into sprite 7 and all others are shifted down.
// Sprite 0 has highest prio.
// 226 LUTs, 68 Slices
module SpriteSet(input clk, input ce,   // Input clock
                 input enable,          // Enable pixel generation
                 input [3:0] load,      // Which parts of the state to load/shift.
                 input [26:0] load_in,  // State to load with 
                 output [4:0] bits,     // Output bits
                 output is_sprite0);    // Set to true if sprite #0 was output

  wire [26:0] load_out7, load_out6, load_out5, load_out4, load_out3, load_out2, load_out1, load_out0; 
  wire [4:0] bits7, bits6, bits5, bits4, bits3, bits2, bits1, bits0;
  Sprite sprite7(clk, ce, enable, load, load_in,   load_out7, bits7);
  Sprite sprite6(clk, ce, enable, load, load_out7, load_out6, bits6);
  Sprite sprite5(clk, ce, enable, load, load_out6, load_out5, bits5);
  Sprite sprite4(clk, ce, enable, load, load_out5, load_out4, bits4);
  Sprite sprite3(clk, ce, enable, load, load_out4, load_out3, bits3);
  Sprite sprite2(clk, ce, enable, load, load_out3, load_out2, bits2);
  Sprite sprite1(clk, ce, enable, load, load_out2, load_out1, bits1);
  Sprite sprite0(clk, ce, enable, load, load_out1, load_out0, bits0);          
  // Determine which sprite is visible on this pixel.
  assign bits = bits0[1:0] != 0 ? bits0 : 
                bits1[1:0] != 0 ? bits1 : 
                bits2[1:0] != 0 ? bits2 : 
                bits3[1:0] != 0 ? bits3 : 
                bits4[1:0] != 0 ? bits4 : 
                bits5[1:0] != 0 ? bits5 : 
                bits6[1:0] != 0 ? bits6 : 
                                  bits7;
  assign is_sprite0 = bits0[1:0] != 0;                             
endmodule  // SpriteSet

module SpriteRAM(input clk, input ce,
                 input reset_line,          // OAM evaluator needs to be reset before processing is started.
                 input sprites_enabled,     // Set to 1 if evaluations are enabled
                 input exiting_vblank,      // Set to 1 when exiting vblank so spr_overflow can be reset
                 input obj_size,            // Set to 1 if objects are 16 pixels.
                 input [8:0] scanline,      // Current scan line (compared against Y)
                 input [8:0] cycle,         // Current cycle.
                 output reg [7:0] oam_bus,  // Current value on the OAM bus, returned to NES through $2004.
                 input oam_ptr_load,        // Load oam with specified value, when writing to NES $2003.
                 input oam_load,            // Load oam_ptr with specified value, when writing to NES $2004.
                 input [7:0] data_in,       // New value for oam or oam_ptr
                 output reg spr_overflow,   // Set to true if we had more than 8 objects on a scan line. Reset when exiting vblank.
                 output reg sprite0);       // True if sprite#0 is included on the scan line currently being painted.
  reg [7:0] sprtemp[0:31];   // Sprite Temporary Memory. 32 bytes.
  reg [7:0] oam[0:255];      // Sprite OAM. 256 bytes.
  reg [7:0] oam_ptr;         // Pointer into oam_ptr.
  reg [2:0] p;               // Upper 3 bits of pointer into temp, the lower bits are oam_ptr[1:0].
  reg [1:0] state;           // Current state machine state
  wire [7:0] oam_data = oam[oam_ptr];
  // Compute the current address we read/write in sprtemp.
  reg [4:0] sprtemp_ptr;
  // Check if the current Y coordinate is inside.
  wire [8:0] spr_y_coord = scanline - {1'b0, oam_data};
  wire spr_is_inside = (spr_y_coord[8:4] == 0) && (obj_size || spr_y_coord[3] == 0);
  reg [7:0] new_oam_ptr;     // [wire] New value for oam ptr
  reg [1:0] oam_inc;         // [wire] How much to increment oam ptr
  reg sprite0_curr;          // If sprite0 is included on the line being processed.
  reg oam_wrapped;           // [wire] if new_oam or new_p wrapped.
  
  wire [7:0] sprtemp_data = sprtemp[sprtemp_ptr];
  always @*  begin
    // Compute address to read/write in temp sprite ram
    casez({cycle[8], cycle[2]}) 
    2'b0_?: sprtemp_ptr = {p, oam_ptr[1:0]};
    2'b1_0: sprtemp_ptr = {cycle[5:3], cycle[1:0]}; // 1-4. Read Y, Tile, Attribs
    2'b1_1: sprtemp_ptr = {cycle[5:3], 2'b11};      // 5-8. Keep reading X.
    endcase
  end
    
  always @* begin
    /* verilator lint_off CASEOVERLAP */
    // Compute value to return to cpu through $2004. And also the value that gets written to temp sprite ram.
    casez({sprites_enabled, cycle[8], cycle[6], state, oam_ptr[1:0]})
    7'b1_10_??_??: oam_bus = sprtemp_data;         // At cycle 256-319 we output what's in sprite temp ram
    7'b1_??_00_??: oam_bus = 8'b11111111;                  // On the first 64 cycles (while inside state 0), we output 0xFF.
    7'b1_??_01_00: oam_bus = {4'b0000, spr_y_coord[3:0]};  // Y coord that will get written to temp ram.
    7'b?_??_??_10: oam_bus = {oam_data[7:5], 3'b000, oam_data[1:0]}; // Bits 2-4 of attrib are always zero when reading oam.
    default:       oam_bus = oam_data;                     // Default to outputting from oam.
    endcase
  end

  always @* begin
    // Compute incremented oam counters
    casez ({oam_load, state, oam_ptr[1:0]})
    5'b1_??_??: oam_inc = {oam_ptr[1:0] == 3, 1'b1};       // Always increment by 1 when writing to oam.
    5'b0_00_??: oam_inc = 2'b01;                           // State 0: On the the first 64 cycles we fill temp ram with 0xFF, increment low bits.
    5'b0_01_00: oam_inc = {!spr_is_inside, spr_is_inside}; // State 1: Copy Y coordinate and increment oam by 1 if it's inside, otherwise 4.
    5'b0_01_??: oam_inc = {oam_ptr[1:0] == 3, 1'b1};       // State 1: Copy remaining 3 bytes of the oam.
    // State 3: We've had more than 8 sprites. Set overflow flag if we found a sprite that overflowed.
    // NES BUG: It increments both low and high counters.
    5'b0_11_??: oam_inc = 2'b11;
    // While in the final state, keep incrementing the low bits only until they're zero.
    5'b0_10_??: oam_inc = {1'b0, oam_ptr[1:0] != 0};
    endcase
    /* verilator lint_on CASEOVERLAP */
    new_oam_ptr[1:0] = oam_ptr[1:0] + {1'b0, oam_inc[0]};
    {oam_wrapped, new_oam_ptr[7:2]} = {1'b0, oam_ptr[7:2]} + {6'b0, oam_inc[1]};
  end
  always @(posedge clk) if (ce) begin
     
    // Some bits of the OAM are hardwired to zero.
    if (oam_load)
      oam[oam_ptr] <= (oam_ptr & 3) == 2 ? data_in & 8'hE3: data_in;
    if (cycle[0] && sprites_enabled || oam_load || oam_ptr_load) begin
      oam_ptr <= oam_ptr_load ? data_in : new_oam_ptr;
    end
    // Set overflow flag?
    if (sprites_enabled && state == 2'b11 && spr_is_inside)
      spr_overflow <= 1;
    // Remember if sprite0 is included on the scanline, needed for hit test later.
    sprite0_curr <= (state == 2'b01 && oam_ptr[7:2] == 0 && spr_is_inside || sprite0_curr);
    
//    if (scanline == 0 && cycle[0] && (state == 2'b01 || state == 2'b00))
//      $write("Drawing sprite %d/%d. bus=%d oam_ptr=%X->%X oam_data=%X p=%d (%d %d %d)\n", scanline, cycle, oam_bus, oam_ptr, new_oam_ptr, oam_data, p,
//         cycle[0] && sprites_enabled, oam_load, oam_ptr_load);
    
    // Always writing to temp ram while we're in state 0 or 1.
    if (!state[1]) sprtemp[sprtemp_ptr] <= oam_bus;
    // Update state machine on every second cycle.
    if (cycle[0]) begin
      // Increment p whenever oam_ptr carries in state 0 or 1.
      if (!state[1] && oam_ptr[1:0] == 2'b11) p <= p + 1;
      // Set sprite0 if sprite1 was included on the scan line
      casez({state, (p == 7) && (oam_ptr[1:0] == 2'b11), oam_wrapped})
      4'b00_0_?: state <= 2'b00;  // State #0: Keep filling
      4'b00_1_?: state <= 2'b01;  // State #0: Until we filled 64 items.
      4'b01_?_1: state <= 2'b10;  // State #1: Goto State 2 if processed all OAM
      4'b01_1_0: state <= 2'b11;  // State #1: Goto State 3 if we found 8 sprites
      4'b01_0_0: state <= 2'b01;  // State #1: Keep comparing Y coordinates.
      4'b11_?_1: state <= 2'b10;  // State #3: Goto State 2 if processed all OAM
      4'b11_?_0: state <= 2'b11;  // State #3: Keep comparing Y coordinates
      4'b10_?_?: state <= 2'b10;  // Stuck in state 2.
      endcase
    end
    if (reset_line) begin
      state <= 0;
      p <= 0;
      oam_ptr <= 0;
      sprite0_curr <= 0;
      sprite0 <= sprite0_curr;
    end
    if (exiting_vblank)
      spr_overflow <= 0;
  end
endmodule  // SpriteRAM


// Generates addresses in VRAM where we'll fetch sprite graphics from,
// and populates load, load_in so the SpriteGen can be loaded.
// 10 LUT, 4 Slices
module SpriteAddressGen(input clk, input ce,
                        input enabled,          // If unset, |load| will be all zeros.
                        input obj_size,         // 0: Sprite Height 8, 1: Sprite Height 16.
                        input obj_patt,         // Object pattern table selection
                        input [2:0] cycle,      // Current load cycle. At #4, first bitmap byte is loaded. At #6, second bitmap byte is.
                        input [7:0] temp,       // Input temp data from SpriteTemp. #0 = Y Coord, #1 = Tile, #2 = Attribs, #3 = X Coord
                        output [12:0] vram_addr,// Low bits of address in VRAM that we'd like to read.
                        input [7:0] vram_data,  // Byte of VRAM in the specified address
                        output [3:0] load,      // Which subset of load_in that is now valid, will be loaded into SpritesGen.
                        output [26:0] load_in); // Bits to load into SpritesGen.
  reg [7:0] temp_tile;    // Holds the tile that we will get
  reg [3:0] temp_y;       // Holds the Y coord (will be swapped based on FlipY).
  reg flip_x, flip_y;     // If incoming bitmap data needs to be flipped in the X or Y direction.
  wire load_y =    (cycle == 0);
  wire load_tile = (cycle == 1);
  wire load_attr = (cycle == 2) && enabled;
  wire load_x =    (cycle == 3) && enabled;
  wire load_pix1 = (cycle == 5) && enabled;
  wire load_pix2 = (cycle == 7) && enabled;
  reg dummy_sprite; // Set if attrib indicates the sprite is invalid.
  // Flip incoming vram data based on flipx. Zero out the sprite if it's invalid. The bits are already flipped once.
  wire [7:0] vram_f = dummy_sprite ? 0 : 
                      !flip_x ?      {vram_data[0], vram_data[1], vram_data[2], vram_data[3], vram_data[4], vram_data[5], vram_data[6], vram_data[7]} : 
                                     vram_data;
  wire [3:0] y_f = temp_y ^ {flip_y, flip_y, flip_y, flip_y};
  assign load = {load_pix1, load_pix2, load_x, load_attr};
  assign load_in = {vram_f, vram_f, temp, temp[1:0], temp[5]};
  // If $2000.5 = 0, the tile index data is used as usual, and $2000.3 
  // selects the pattern table to use. If $2000.5 = 1, the MSB of the range 
  // result value become the LSB of the indexed tile, and the LSB of the tile 
  // index value determines pattern table selection. The lower 3 bits of the 
  // range result value are always used as the fine vertical offset into the 
  // selected pattern.
  assign vram_addr = {obj_size ? temp_tile[0] : obj_patt, 
                      temp_tile[7:1], obj_size ? y_f[3] : temp_tile[0], cycle[1], y_f[2:0] };
  always @(posedge clk) if (ce) begin
    if (load_y) temp_y <= temp[3:0];
    if (load_tile) temp_tile <= temp;
    if (load_attr) {flip_y, flip_x, dummy_sprite} <= {temp[7:6], temp[4]};
  end
//  always @(posedge clk) begin
//    if (load[3]) $write("Loading pix1: %x\n", load_in[26:19]);
//    if (load[2]) $write("Loading pix2: %x\n", load_in[18:11]);
//    if (load[1]) $write("Loading x: %x\n", load_in[10:3]);
//
//    if (valid_sprite && enabled)
//      $write("%d. Found %d. Flip:%d%d, Addr: %x, Vram: %x!\n", cycle, temp, flip_x, flip_y, vram_addr, vram_data);
//  end

endmodule  // SpriteAddressGen

module BgPainter(input clk, input ce,
                 input enable,             // Shift registers activated
                 input [2:0] cycle,
                 input [2:0] fine_x_scroll,
                 input [14:0] loopy,
                 output [7:0] name_table,  // VRAM name table to read next.
                 input [7:0] vram_data,
                 output [3:0] pixel);
  reg [15:0] playfield_pipe_1; // Name table pixel pipeline #1
  reg [15:0] playfield_pipe_2; // Name table pixel pipeline #2
  reg [8:0]  playfield_pipe_3; // Attribute table pixel pipe #1
  reg [8:0]  playfield_pipe_4; // Attribute table pixel pipe #2
  reg [7:0] current_name_table;      // Holds the current name table byte
  reg [1:0] current_attribute_table; // Holds the 2 current attribute table bits
  reg [7:0] bg0;                // Pixel data for last loaded background
  wire [7:0] bg1 =  vram_data;
  initial begin
    playfield_pipe_1 = 0;
    playfield_pipe_2 = 0;
    playfield_pipe_3 = 0;
    playfield_pipe_4 = 0;
    current_name_table = 0;
    current_attribute_table = 0;
    bg0 = 0;
  end
  always @(posedge clk) if (ce) begin
    case (cycle[2:0])
    1: current_name_table <= vram_data;
    3: current_attribute_table <= (!loopy[1] && !loopy[6]) ? vram_data[1:0] : 
                                  ( loopy[1] && !loopy[6]) ? vram_data[3:2] :
                                  (!loopy[1] &&  loopy[6]) ? vram_data[5:4] : 
                                                             vram_data[7:6];
    5: bg0 <= vram_data; // Pattern table bitmap #0
//    7: bg1 <= vram_data; // Pattern table bitmap #1
    endcase
    if (enable) begin
      playfield_pipe_1[14:0] <= playfield_pipe_1[15:1];
      playfield_pipe_2[14:0] <= playfield_pipe_2[15:1];
      playfield_pipe_3[7:0] <= playfield_pipe_3[8:1];
      playfield_pipe_4[7:0] <= playfield_pipe_4[8:1];
      // Load the new values into the shift registers at the last pixel.
      if (cycle[2:0] == 7) begin
        playfield_pipe_1[15:8] <= {bg0[0], bg0[1], bg0[2], bg0[3], bg0[4], bg0[5], bg0[6], bg0[7]};
        playfield_pipe_2[15:8] <= {bg1[0], bg1[1], bg1[2], bg1[3], bg1[4], bg1[5], bg1[6], bg1[7]};
        playfield_pipe_3[8] <= current_attribute_table[0];
        playfield_pipe_4[8] <= current_attribute_table[1];
      end
    end
  end
  assign name_table = current_name_table;
  wire [3:0] i = {1'b0, fine_x_scroll};
  assign pixel = {playfield_pipe_4[i], playfield_pipe_3[i],
                  playfield_pipe_2[i], playfield_pipe_1[i]};
endmodule  // BgPainter
 
module PixelMuxer(input [3:0] bg, input [3:0] obj, input obj_prio, output [3:0] out, output is_obj);
  wire bg_flag = bg[0] | bg[1];
  wire obj_flag = obj[0] | obj[1];
  assign is_obj = !(obj_prio && bg_flag) && obj_flag;
  assign out = is_obj ? obj : bg;
endmodule
 

module PaletteRam(input clk, input ce, input [4:0] addr, input [5:0] din, output [5:0] dout, input write);
  reg [5:0] palette [0:31];
  initial begin
     $readmemh("design03-data0.hex", palette);
  end
  // Force read from backdrop channel if reading from any addr 0.
  wire [4:0] addr2 = (addr[1:0] == 0) ? 0 : addr;
  assign dout = palette[addr2];
  always @(posedge clk) if (ce && write) begin
    // Allow writing only to x0
    if (!(addr[3:2] != 0 && addr[1:0] == 0))
      palette[addr2] <= din;
  end
endmodule  // PaletteRam
 
module PPU(input clk, input ce, input reset,   // input clock  21.48 MHz / 4. 1 clock cycle = 1 pixel
           output [5:0] color, // output color value, one pixel outputted every clock
           input [7:0] din,   // input data from bus
           output [7:0] dout, // output data to CPU
           input [2:0] ain,   // input address from CPU
           input read,        // read
           input write,       // write
           output nmi,    // one while inside vblank
           output vram_r, // read from vram active
           output vram_w, // write to vram active
           output [13:0] vram_a, // vram address
           input [7:0] vram_din, // vram input
           output [7:0] vram_dout,
           output [8:0] scanline,
           output [8:0] cycle,
           output [19:0] mapper_ppu_flags);
  // These are stored in control register 0
  reg obj_patt; // Object pattern table
  reg bg_patt;  // Background pattern table
  reg obj_size; // 1 if sprites are 16 pixels high, else 0.
  reg vbl_enable;  // Enable VBL flag
  // These are stored in control register 1
  reg grayscale; // Disable color burst
  reg playfield_clip;     // 0: Left side 8 pixels playfield clipping
  reg object_clip;        // 0: Left side 8 pixels object clipping
  reg enable_playfield;   // Enable playfield display
  reg enable_objects;     // Enable objects display
  reg [2:0] color_intensity; // Color intensity
  
  initial begin
    obj_patt = 0;
    bg_patt = 0;
    obj_size = 0;
    vbl_enable = 0;
    grayscale = 0;
    playfield_clip = 0;
    object_clip = 0;
    enable_playfield = 0;
    enable_objects = 0;
    color_intensity = 0;
  end
  
  reg nmi_occured;         // True if NMI has occured but not cleared.
  reg [7:0] vram_latch;
  // Clock generator
  wire is_in_vblank;        // True if we're in VBLANK
  //wire [8:0] scanline;      // Current scanline
  //wire [8:0] cycle;         // Current cycle inside of the line
  wire end_of_line;         // At the last pixel of a line
  wire at_last_cycle_group; // At the very last cycle group of the scan line.
  wire exiting_vblank;      // At the very last cycle of the vblank
  wire entering_vblank;     // 
  wire is_pre_render_line;  // True while we're on the pre render scanline
  wire is_rendering = (enable_playfield || enable_objects) && !is_in_vblank && scanline != 240;
  
  ClockGen clock(clk, ce, reset, is_rendering, scanline, cycle, is_in_vblank, end_of_line, at_last_cycle_group,
                 exiting_vblank, entering_vblank, is_pre_render_line);
  
  
  // The loopy module handles updating of the loopy address
  wire [14:0] loopy;
  wire [2:0] fine_x_scroll;
  LoopyGen loopy0(clk, ce, is_rendering, ain, din, read, write, is_pre_render_line, cycle, loopy, fine_x_scroll);
  // Set to true if the current ppu_addr pointer points into
  // palette ram.
  wire is_pal_address = (loopy[13:8] == 6'b111111);

  // Paints background
  wire [7:0] bg_name_table;
  wire [3:0] bg_pixel_noblank;
  BgPainter bg_painter(clk, ce, !at_last_cycle_group, cycle[2:0], fine_x_scroll, loopy, bg_name_table, vram_din, bg_pixel_noblank);
  
  // Blank out BG in the leftmost 8 pixels?
  wire show_bg_on_pixel = (playfield_clip || (cycle[7:3] != 0)) && enable_playfield;
  wire [3:0] bg_pixel = {bg_pixel_noblank[3:2], show_bg_on_pixel ? bg_pixel_noblank[1:0] : 2'b00};

  // This will set oam_ptr to 0 right before the scanline 240 and keep it there throughout vblank.
  wire before_line = (enable_playfield || enable_objects) && (exiting_vblank || end_of_line && !is_in_vblank);
  wire [7:0] oam_bus;
  wire sprite_overflow;
  wire obj0_on_line;                        // True if sprite#0 is included on the current line
  SpriteRAM sprite_ram(clk, ce,
                       before_line,         // Condition for resetting the sprite line state.
                       is_rendering,        // Condition for enabling sprite ram logic. Check so we're not on 
                       exiting_vblank,
                       obj_size,
                       scanline, cycle,
                       oam_bus,
                       write && (ain == 3), // Write to oam_ptr
                       write && (ain == 4), // Write to oam[oam_ptr]
                       din,
                       sprite_overflow,
                       obj0_on_line);
  wire [4:0] obj_pixel_noblank;
  wire [12:0] sprite_vram_addr;
  wire is_obj0_pixel;               // True if obj_pixel originates from sprite0.
  wire [3:0] spriteset_load;          // Which subset of the |load_in| to load into SpriteSet
  wire [26:0] spriteset_load_in;      // Bits to load into SpriteSet
  // Between 256..319 (64 cycles), fetches bitmap data for the 8 sprites and fills in the SpriteSet
  // so that it can start drawing on the next frame.
  SpriteAddressGen address_gen(clk, ce,
                               cycle[8] && !cycle[6],     // Load sprites between 256..319
                               obj_size, obj_patt,        // Object size and pattern table
                               cycle[2:0],                // Cycle counter
                               oam_bus,                   // Info from temp buffer.
                               sprite_vram_addr,          // [out] VRAM Address that we want data from
                               vram_din,                  // [in] Data at the specified address
                               spriteset_load,
                               spriteset_load_in);        // Which parts of SpriteGen to load
  // Between 0..255 (256 cycles), draws pixels.
  // Between 256..319 (64 cycles), will be populated for next line
  SpriteSet sprite_gen(clk, ce, !cycle[8], spriteset_load, spriteset_load_in, obj_pixel_noblank, is_obj0_pixel);
  // Blank out obj in the leftmost 8 pixels?    
  wire show_obj_on_pixel = (object_clip || (cycle[7:3] != 0)) && enable_objects;
  wire [4:0] obj_pixel = {obj_pixel_noblank[4:2], show_obj_on_pixel ? obj_pixel_noblank[1:0] : 2'b00};
  
  reg sprite0_hit_bg;            // True if sprite#0 has collided with the BG in the last frame.
  always @(posedge clk) if (ce) begin
    if (exiting_vblank)
      sprite0_hit_bg <= 0;
    else if (is_rendering &&         // Object rendering is enabled
             !cycle[8] &&            // X Pixel 0..255
             cycle[7:0] != 255 &&    // X pixel != 255
             !is_pre_render_line &&  // Y Pixel 0..239
             obj0_on_line &&         // True if sprite#0 is included on the scan line.
             is_obj0_pixel &&        // True if the pixel came from tempram #0.
             show_obj_on_pixel &&
             bg_pixel[1:0] != 0) begin // Background pixel nonzero.
      sprite0_hit_bg <= 1;
      
    end

//    if (!cycle[8] && is_visible_line && obj0_on_line && is_obj0_pixel)
//      $write("Sprite0 hit bg scan %d!!\n", scanline);

//    if (is_obj0_pixel)
//      $write("drawing obj0 pixel %d/%d\n", scanline, cycle);
  end
 
  wire [3:0] pixel;
  wire pixel_is_obj;
  PixelMuxer pixel_muxer(bg_pixel, obj_pixel[3:0], obj_pixel[4], pixel, pixel_is_obj);
 
  // Compute the value to put on the VRAM address bus
  assign vram_a = !is_rendering    ? loopy[13:0] : // VRAM
                  (cycle[2:1] == 0)     ? {2'b10, loopy[11:0]} : // Name table
                  (cycle[2:1] == 1)     ? {2'b10, loopy[11:10], 4'b1111, loopy[9:7], loopy[4:2]} : // Attribute table
                  cycle[8] && !cycle[6] ? {1'b0, sprite_vram_addr} : 
                                          {1'b0, bg_patt, bg_name_table, cycle[1], loopy[14:12]}; // Pattern table bitmap #0, #1
  // Read from VRAM, either when user requested a manual read, or when we're generating pixels.
  assign vram_r = read && (ain == 7) ||
                  is_rendering && cycle[0] == 0 && !end_of_line;
  
  // Write to VRAM?
  assign vram_w = write && (ain == 7) && !is_pal_address && !is_rendering;

  wire [5:0] color2;
  PaletteRam palette_ram(clk, ce, 
                         is_rendering ? {pixel_is_obj, pixel[3:0]} : (is_pal_address ? loopy[4:0] : 5'b0000), // Read addr
                         din[5:0], // Value to write
                         color2,    // Output color
                         write && (ain == 7) && is_pal_address); // Condition for writing
  assign color = grayscale ? {color2[5:4], 4'b0} : color2;
//  always @(posedge clk)  
//  if (scanline == 194 && cycle < 8 && color == 15) begin
//    $write("Pixel black %x %x %x %x %x\n", bg_pixel,obj_pixel,pixel,pixel_is_obj,color);
//  end

 
  always @(posedge clk) if (ce) begin
//    if (!is_in_vblank && write)
//      $write("%d/%d: $200%d <= %x\n", scanline, cycle, ain, din);
    if (write) begin
      case (ain)
      0: begin // PPU Control Register 1
      // t:....BA.. ........ = d:......BA
        obj_patt <= din[3];
        bg_patt <= din[4];
        obj_size <= din[5];
        vbl_enable <= din[7];
        
        //$write("PPU Control #0 <= %X\n", din);
      end
      1: begin // PPU Control Register 2
        grayscale <= din[0];
        playfield_clip <= din[1];
        object_clip <= din[2];
        enable_playfield <= din[3];
        enable_objects <= din[4];
        color_intensity <= din[7:5];
        if (!din[3] && scanline == 59)
          $write("Disabling playfield at cycle %d\n", cycle);
      end
      endcase
    end
     
    // Reset frame specific counters upon exiting vblank
    if (exiting_vblank)
      nmi_occured <= 0;
    // Set the 
    if (entering_vblank)
      nmi_occured <= 1;
    // Reset NMI register when reading from Status
    if (read && ain == 2)
      nmi_occured <= 0;
  end
  
  // If we're triggering a VBLANK NMI 
  assign nmi = nmi_occured && vbl_enable;

  // One cycle after vram_r was asserted, the value
  // is available on the bus.
  reg vram_read_delayed;
  always @(posedge clk) if (ce) begin
    if (vram_read_delayed)
      vram_latch <= vram_din;
    vram_read_delayed = vram_r;
  end
  
  // Value currently being written to video ram
  assign vram_dout = din;

  reg [7:0] latched_dout;
  always @* begin
    case (ain)
    2: latched_dout = {nmi_occured,
               sprite0_hit_bg,
               sprite_overflow,
               5'b00000};
    4: latched_dout = oam_bus;
    default: if (is_pal_address) begin
        latched_dout = {2'b00, color};
      end else begin
        latched_dout = vram_latch;
      end 
    endcase
  end
  
  assign dout = latched_dout;
  
  
  assign mapper_ppu_flags = {scanline, cycle, obj_size, is_rendering};

endmodule  // PPU
// Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.

//`include "cpu.v"
//`include "apu.v"
//`include "ppu.v"
//`include "mmu.v"

// Sprite DMA Works as follows.
// When the CPU writes to $4014 DMA is initiated ASAP.
// DMA runs for 512 cycles, the first cycle it reads from address
// xx00 - xxFF, into a latch, and the second cycle it writes to $2004.

// Facts:
// 1) Sprite DMA always does reads on even cycles and writes on odd cycles.
// 2) There are 1-2 cycles of cpu_read=1 after cpu_read=0 until Sprite DMA starts (pause_cpu=1, aout_enable=0)
// 3) Sprite DMA reads the address value on the last clock of cpu_read=0

/*

=== DMC State Machine ===

// 
if (dmc_state == 0 && dmc_trigger && cpu_read && !odd_cycle) dmc_state <= 1;
if (dmc_state == 1) dmc_state <= (spr_state[1] ? 3 : 2);
pause_cpu = dmc_state[1] && cpu_read;
if (dmc_state == 2 && cpu_read && !odd_cycle) dmc_state <= 3;
aout_enable = (dmc_state == 3 && !odd_cycle)
dmc_ack     = (dmc_state == 3 && !odd_cycle)
read        = 1
if (dmc_state == 3 && !odd_cycle) dmc_state <= 0;

== Sprite State Machine ==
if (sprite_trigger) { sprite_dma_addr <= data_from_cpu; spr_state <= 1; }
pause_cpu = spr_state[0] && cpu_read;
if (spr_state == 1 && cpu_read && odd_cycle) spr_state <= 3;
if (spr_state == 3 && !odd_cycle) { if (dmc_state == 3) spr_state <= 1; else DO_READ; }
if (spr_state == 3 && odd_cycle) { DO_WRITE; }


// 4) If DMC interrupts Sprite, then it runs on the even cycle, and the odd cycle will be idle (pause_cpu=1, aout_enable=0)
// 5) When DMC triggers && interrupts CPU, there will be 2-3 cycles (pause_cpu=1, aout_enable=0) before DMC DMA starts.
*/


module DmaController(input clk, input ce, input reset,
                     input odd_cycle,               // Current cycle even or odd?
                     input sprite_trigger,          // Sprite DMA trigger?
                     input dmc_trigger,             // DMC DMA trigger?
                     input cpu_read,                // CPU is in a read cycle?
                     input [7:0] data_from_cpu,     // Data written by CPU?
                     input [7:0] data_from_ram,     // Data read from RAM?
                     input [15:0] dmc_dma_addr,     // DMC DMA Address
                     output [15:0] aout,            // Address to access
                     output aout_enable,            // DMA controller wants bus control
                     output read,                   // 1 = read, 0 = write
                     output [7:0] data_to_ram,      // Value to write to RAM
                     output dmc_ack,                // ACK the DMC DMA
                     output pause_cpu);             // CPU is paused
  reg dmc_state;
  reg [1:0] spr_state;
  reg [7:0] sprite_dma_lastval;
  reg [15:0] sprite_dma_addr;     // sprite dma source addr
  wire [8:0] new_sprite_dma_addr = sprite_dma_addr[7:0] + 8'h01;
  always @(posedge clk) if (reset) begin
    dmc_state <= 0;
    spr_state <= 0;    
    sprite_dma_lastval <= 0;
    sprite_dma_addr <= 0;
  end else if (ce) begin
    if (dmc_state == 0 && dmc_trigger && cpu_read && !odd_cycle) dmc_state <= 1;
    if (dmc_state == 1 && !odd_cycle) dmc_state <= 0;
    
    if (sprite_trigger) begin sprite_dma_addr <= {data_from_cpu, 8'h00}; spr_state <= 1; end
    if (spr_state == 1 && cpu_read && odd_cycle) spr_state <= 3;
    if (spr_state[1] && !odd_cycle && dmc_state == 1) spr_state <= 1;
    if (spr_state[1] && odd_cycle) sprite_dma_addr[7:0] <= new_sprite_dma_addr[7:0];
    if (spr_state[1] && odd_cycle && new_sprite_dma_addr[8]) spr_state <= 0;
    if (spr_state[1]) sprite_dma_lastval <= data_from_ram;
  end
  assign pause_cpu = (spr_state[0] || dmc_trigger) && cpu_read;
  assign dmc_ack   = (dmc_state == 1 && !odd_cycle);
  assign aout_enable = dmc_ack || spr_state[1];
  assign read = !odd_cycle;
  assign data_to_ram = sprite_dma_lastval;
  assign aout = dmc_ack ? dmc_dma_addr : !odd_cycle ? sprite_dma_addr : 16'h2004;
endmodule

// Multiplexes accesses by the PPU and the PRG into a single memory, used for both
// ROM and internal memory.
// PPU has priority, its read/write will be honored asap, while the CPU's reads
// will happen only every second cycle when the PPU is idle.
// Data read by PPU will be available on the next clock cycle.
// Data read by CPU will be available within at most 2 clock cycles.

module MemoryMultiplex(input clk, input ce, input reset,
                       input [21:0] prg_addr, input prg_read, input prg_write, input [7:0] prg_din,
                       input [21:0] chr_addr, input chr_read, input chr_write, input [7:0] chr_din,
                       // Access signals for the SRAM.
                       output [21:0] memory_addr,   // address to access
                       output memory_read_cpu,      // read into CPU latch
                       output memory_read_ppu,      // read into PPU latch
                       output memory_write,         // is a write operation
                       output [7:0] memory_dout);
  reg saved_prg_read, saved_prg_write;
  assign memory_addr = (chr_read || chr_write) ? chr_addr : prg_addr;
  assign memory_write = (chr_read || chr_write) ? chr_write : saved_prg_write;
  assign memory_read_ppu = chr_read;
  assign memory_read_cpu = !(chr_read || chr_write) && (prg_read || saved_prg_read);
  assign memory_dout = chr_write ? chr_din : prg_din;
  always @(posedge clk) if (reset) begin
		saved_prg_read <= 0;
		saved_prg_write <= 0;
  end else if (ce) begin
    if (chr_read || chr_write) begin
      saved_prg_read <= prg_read || saved_prg_read;
      saved_prg_write <= prg_write || saved_prg_write;
    end else begin
      saved_prg_read <= 0;
      saved_prg_write <= prg_write;
    end
  end
endmodule


module NES(input clk, input reset, input ce,
           input [31:0] mapper_flags,
           output [15:0] sample, // sample generated from APU
           output [5:0] color,  // pixel generated from PPU
           output joypad_strobe,// Set to 1 to strobe joypads. Then set to zero to keep the value.
           output [1:0] joypad_clock, // Set to 1 for each joypad to clock it.
           input [3:0] joypad_data, // Data for each joypad + 1 powerpad.
           input [4:0] audio_channels, // Enabled audio channels

           
           // Access signals for the SRAM.
           output [21:0] memory_addr,   // address to access
           output memory_read_cpu,      // read into CPU latch
           input [7:0] memory_din_cpu,  // next cycle, contents of latch A (CPU's data)
           output memory_read_ppu,      // read into CPU latch
           input [7:0] memory_din_ppu,  // next cycle, contents of latch B (PPU's data)
           output memory_write,         // is a write operation
           output [7:0] memory_dout,
           
           output [8:0] cycle,
           output [8:0] scanline,
           
           output reg [31:0] dbgadr,
           output [1:0] dbgctr
           );
  reg [7:0] from_data_bus;
  wire [7:0] cpu_dout;
  wire odd_or_even; // Is this an odd or even clock cycle?

  // The CPU runs at one third the speed of the PPU.
  // CPU is clocked at cycle #2. PPU is clocked at cycle #0, #1, #2.
  // CPU does its memory I/O on cycle #0. It will be available in time for cycle #2.
  reg [1:0] cpu_cycle_counter;
  always @(posedge clk) begin
    if (reset)
      cpu_cycle_counter <= 0;
    else if (ce)
      cpu_cycle_counter <= (cpu_cycle_counter == 2) ? 0 : cpu_cycle_counter + 1;
  end

  // Sample the NMI flag on cycle #0, otherwise if NMI happens on cycle #0 or #1,
  // the CPU will use it even though it shouldn't be used until the next CPU cycle.
  wire nmi;
  reg nmi_active;
  always @(posedge clk) begin
    if (reset)
      nmi_active <= 0;
    else if (ce && cpu_cycle_counter == 0)
      nmi_active <= nmi;
  end

  wire apu_ce =        ce && (cpu_cycle_counter == 2);

  // -- CPU
  wire [15:0] cpu_addr;
  wire cpu_mr, cpu_mw;
  wire pause_cpu;
  reg apu_irq_delayed;
  reg mapper_irq_delayed;
  CPU cpu(clk, apu_ce && !pause_cpu, reset, from_data_bus, apu_irq_delayed | mapper_irq_delayed, nmi_active, cpu_dout, cpu_addr, cpu_mr, cpu_mw);

  // -- DMA
  wire [15:0] dma_aout;
  wire dma_aout_enable;
  wire dma_read;
  wire [7:0] dma_data_to_ram;
  wire apu_dma_request, apu_dma_ack;
  wire [15:0] apu_dma_addr;

  // Determine the values on the bus outgoing from the CPU chip (after DMA / APU)
  wire [15:0] addr = dma_aout_enable ? dma_aout : cpu_addr;
  wire [7:0]  dbus = dma_aout_enable ? dma_data_to_ram : cpu_dout;
  wire mr_int      = dma_aout_enable ? dma_read : cpu_mr;
  wire mw_int      = dma_aout_enable ? !dma_read : cpu_mw;

  DmaController dma(clk, apu_ce, reset, 
                    odd_or_even,                    // Even or odd cycle
                    (addr == 'h4014 && mw_int),     // Sprite trigger
                    apu_dma_request,                // DMC Trigger
                    cpu_mr,                         // CPU in a read cycle?
                    cpu_dout,                       // Data from cpu
                    from_data_bus,                  // Data from RAM etc.
                    apu_dma_addr,                   // DMC addr
                    dma_aout,
                    dma_aout_enable, 
                    dma_read,
                    dma_data_to_ram,
                    apu_dma_ack,
                    pause_cpu);

  // -- Audio Processing Unit  
  wire apu_cs = addr >= 'h4000 && addr < 'h4018;
  wire [7:0] apu_dout;
  wire apu_irq;
  APU apu(clk, apu_ce, reset,
          addr[4:0], dbus, apu_dout, 
          mw_int && apu_cs, mr_int && apu_cs,
          audio_channels,
          sample,
          apu_dma_request,
          apu_dma_ack,
          apu_dma_addr,
          from_data_bus,
          odd_or_even,
          apu_irq);

  // Joypads are mapped into the APU's range.
  wire joypad1_cs = (addr == 'h4016);
  wire joypad2_cs = (addr == 'h4017);
  assign joypad_strobe = (joypad1_cs && mw_int && cpu_dout[0]);
  assign joypad_clock =  {joypad2_cs && mr_int, joypad1_cs && mr_int};

      
  // -- PPU
  // PPU _reads_ need to happen on the same cycle the cpu runs on, to guarantee we
  // see proper values of register $2002.
  wire mr_ppu     = mr_int && (cpu_cycle_counter == 2);
  wire mw_ppu     = mw_int && (cpu_cycle_counter == 0);
  wire ppu_cs = addr >= 'h2000 && addr < 'h4000;
  wire [7:0] ppu_dout;           // Data from PPU to CPU
  wire chr_read, chr_write;      // If PPU reads/writes from VRAM
  wire [13:0] chr_addr;          // Address PPU accesses in VRAM
  wire [7:0] chr_from_ppu;       // Data from PPU to VRAM
  wire [7:0] chr_to_ppu;
  wire [19:0] mapper_ppu_flags;  // PPU flags for mapper cheating
  PPU ppu(clk, ce, reset, color, dbus, ppu_dout, addr[2:0],
          ppu_cs && mr_ppu, ppu_cs && mw_ppu,
          nmi,
          chr_read, chr_write, chr_addr, chr_to_ppu, chr_from_ppu,
          scanline, cycle, mapper_ppu_flags);

  // -- Memory mapping logic
  wire [15:0] prg_addr = addr;
  wire [7:0] prg_din = dbus;
  wire prg_read = mr_int && (cpu_cycle_counter == 0) && !apu_cs && !ppu_cs;
  wire prg_write = mw_int && (cpu_cycle_counter == 0) && !apu_cs && !ppu_cs;
  wire prg_allow, vram_a10, vram_ce, chr_allow;
  wire [21:0] prg_linaddr, chr_linaddr;
  wire [7:0] prg_dout_mapper, chr_from_ppu_mapper;
  wire cart_ce = (cpu_cycle_counter == 0) && ce;
  wire mapper_irq;
  wire has_chr_from_ppu_mapper;
  MultiMapper multi_mapper(clk, cart_ce, ce, reset, mapper_ppu_flags, mapper_flags, 
                           prg_addr, prg_linaddr, prg_read, prg_write, prg_din, prg_dout_mapper, from_data_bus, prg_allow,
                           chr_read, chr_addr, chr_linaddr, chr_from_ppu_mapper, has_chr_from_ppu_mapper, chr_allow, vram_a10, vram_ce, mapper_irq);
  assign chr_to_ppu = has_chr_from_ppu_mapper ? chr_from_ppu_mapper : memory_din_ppu;
                             
  // Mapper IRQ seems to be delayed by one PPU clock.   
  // APU IRQ seems delayed by one APU clock.
  always @(posedge clk) if (reset) begin
    mapper_irq_delayed <= 0;
    apu_irq_delayed <= 0;
  end else begin
    if (ce)
      mapper_irq_delayed <= mapper_irq;
    if (apu_ce)
      apu_irq_delayed <= apu_irq;
  end
   
  // -- Multiplexes CPU and PPU accesses into one single RAM
  MemoryMultiplex mem(clk, ce, reset, prg_linaddr, prg_read && prg_allow, prg_write && prg_allow, prg_din, 
                               chr_linaddr, chr_read,              chr_write && (chr_allow || vram_ce), chr_from_ppu,
                               memory_addr, memory_read_cpu, memory_read_ppu, memory_write, memory_dout);

  always @* begin
    if (reset)
		from_data_bus <= 0;
    else if (apu_cs) begin
      if (joypad1_cs)
        from_data_bus = {7'b0100000, joypad_data[0]};
      else if (joypad2_cs)
        from_data_bus = {3'b010, joypad_data[3:2] ,2'b00, joypad_data[1]};
      else
        from_data_bus = apu_dout;
    end else if (ppu_cs) begin
      from_data_bus = ppu_dout;
    end else if (prg_allow) begin
      from_data_bus = memory_din_cpu;
    end else begin
      from_data_bus = prg_dout_mapper;
    end
  end
  
endmodule
// Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.

//`include "MicroCode.v"

module MyAddSub(input [7:0] A,B,
                input CI,ADD,
                output [7:0] S,
                output CO,OFL);
  wire C0,C1,C2,C3,C4,C5,C6;
  wire C6O;
  wire [7:0] I = A ^ B ^ {8{~ADD}};
  MUXCY_L MUXCY_L0 (.LO(C0),.CI(CI),.DI(A[0]),.S(I[0]) );
  MUXCY_L MUXCY_L1 (.LO(C1),.CI(C0),.DI(A[1]),.S(I[1]) );
  MUXCY_L MUXCY_L2 (.LO(C2),.CI(C1),.DI(A[2]),.S(I[2]) );
  MUXCY_L MUXCY_L3 (.LO(C3),.CI(C2),.DI(A[3]),.S(I[3]) );
  MUXCY_L MUXCY_L4 (.LO(C4),.CI(C3),.DI(A[4]),.S(I[4]) );
  MUXCY_L MUXCY_L5 (.LO(C5),.CI(C4),.DI(A[5]),.S(I[5]) );
  MUXCY_D MUXCY_D6 (.LO(C6),.O(C6O),.CI(C5),.DI(A[6]),.S(I[6]) );
  MUXCY   MUXCY_7  (.O(CO),.CI(C6),.DI(A[7]),.S(I[7]) );
  XORCY XORCY0 (.O(S[0]),.CI(CI),.LI(I[0]));
  XORCY XORCY1 (.O(S[1]),.CI(C0),.LI(I[1]));
  XORCY XORCY2 (.O(S[2]),.CI(C1),.LI(I[2]));
  XORCY XORCY3 (.O(S[3]),.CI(C2),.LI(I[3]));
  XORCY XORCY4 (.O(S[4]),.CI(C3),.LI(I[4]));
  XORCY XORCY5 (.O(S[5]),.CI(C4),.LI(I[5]));
  XORCY XORCY6 (.O(S[6]),.CI(C5),.LI(I[6]));
  XORCY XORCY7 (.O(S[7]),.CI(C6),.LI(I[7]));
  XOR2 X1(.O(OFL),.I0(C6O),.I1(CO));
endmodule

module NewAlu(input  [10:0] OP, // ALU Operation
           input  [7:0] A,   // Registers input
           input  [7:0] X,   //       ""
           input  [7:0] Y,   //       ""
           input  [7:0] S,   //       ""
           input  [7:0] M,  // Secondary input to ALU
           input  [7:0] T,  // Secondary input to ALU
                             // -- Flags Input
           input        CI,  // Carry In
           input        VI,  // Overflow In
                             // -- Flags output
           output reg   CO,  // Carry out
           output reg   VO,  // Overflow out
           output reg   SO,  // Sign out
           output reg   ZO,  // zero out
                             // -- Result output
           output reg [7:0] Result,// Result out
           output reg [7:0] IntR); // Intermediate result out
  // Crack the ALU Operation
  wire [1:0] o_left_input, o_right_input;
  wire [2:0] o_first_op, o_second_op;
  wire o_fc;
  assign {o_left_input, o_right_input, o_first_op, o_second_op, o_fc} = OP;
  
  // Determine left, right inputs to Add/Sub ALU.
  reg [7:0] L, R;
  reg CR;
  always begin
    casez(o_left_input)
    0: L = A;
    1: L = Y;
    2: L = X;
    3: L = A & X;
    endcase
    casez(o_right_input)
    0: R = M;
    1: R = T;
    2: R = L;
    3: R = S;
    endcase
    CR = CI;
    casez(o_first_op[2:1])
    0: {CR, IntR} = {R, CI & o_first_op[0]};  // SHL, ROL
    1: {IntR, CR} = {CI & o_first_op[0], R};  // SHR, ROR
    2: IntR = R;                              // Passthrough
    3: IntR = R + (o_first_op[0] ? 8'b1 : 8'b11111111); // INC/DEC
    endcase
  end
  wire [7:0] AddR;
  wire AddCO, AddVO;
  MyAddSub addsub(.A(L),.B(IntR),.CI(o_second_op[0] ? CR : 1'b1),.ADD(!o_second_op[2]), .S(AddR), .CO(AddCO), .OFL(AddVO));
  // Produce the output of the second stage.
  always begin
    casez(o_second_op)
    0:       {CO, Result} = {CR,    L | IntR};
    1:       {CO, Result} = {CR,    L & IntR};
    2:       {CO, Result} = {CR,    L ^ IntR};
    3, 6, 7: {CO, Result} = {AddCO, AddR};
    4, 5:    {CO, Result} = {CR,    IntR};
    endcase
    // Final result
    ZO = (Result == 0);
    // Compute overflow flag
    VO = VI;
    casez(o_second_op)
    1: if (!o_fc) VO = IntR[6]; // Set V to 6th bit for BIT
    3: VO = AddVO;              // ADC always sets V
    7: if (o_fc) VO = AddVO;    // Only SBC sets V.
    endcase
    // Compute sign flag. It's always the uppermost bit of the result,
    // except for BIT that sets it to the 7th input bit
    SO = (o_second_op == 1 && !o_fc) ? IntR[7] : Result[7];
  end
endmodule

module AddressGenerator(input clk, input ce,
                        input [4:0] Operation, 
                        input [1:0] MuxCtrl,
                        input [7:0] DataBus, T, X, Y,
                        output [15:0] AX,
                        output Carry);
  // Actual contents of registers
  reg [7:0] AL, AH;
  // Last operation generated a carry?
  reg SavedCarry;
  assign AX = {AH, AL};

  wire [2:0] ALCtrl = Operation[4:2];
  wire [1:0] AHCtrl = Operation[1:0];

  // Possible new value for AL.
  wire [7:0] NewAL;
  assign {Carry,NewAL} = {1'b0, (MuxCtrl[1] ? T : AL)} + {1'b0, (MuxCtrl[0] ? Y : X)};
  
  // The other one
  wire TmpVal = (!AHCtrl[1] | SavedCarry);
  wire [7:0] TmpAdd = (AHCtrl[1] ? AH : AL) + {7'b0, TmpVal};
  
  always @(posedge clk) if (ce) begin
    SavedCarry <= Carry;
    if (ALCtrl[2])
      case(ALCtrl[1:0])
      0: AL <= NewAL;
      1: AL <= DataBus;
      2: AL <= TmpAdd;
      3: AL <= T;
      endcase
     
    case(AHCtrl[1:0])
    0: AH <= AH;
    1: AH <= 0;
    2: AH <= TmpAdd;
    3: AH <= DataBus;
    endcase
  end
endmodule

module ProgramCounter(input clk, input ce,
                      input [1:0] LoadPC,
                      input GotInterrupt,
                      input [7:0] DIN,
                      input [7:0] T,
                      output reg [15:0] PC, output JumpNoOverflow);
  reg [15:0] NewPC;
  assign JumpNoOverflow = ((PC[8] ^ NewPC[8]) == 0) & LoadPC[0] & LoadPC[1];

  always begin
    // Load PC Control
    case (LoadPC) 
    0,1: NewPC = PC + {15'b0, (LoadPC[0] & ~GotInterrupt)};
    2:   NewPC = {DIN,T};
    3:   NewPC = PC + {{8{T[7]}},T};
    endcase
  end
  
  always @(posedge clk)
    if (ce)
      PC <= NewPC;    
endmodule


module CPU(input clk, input ce, input reset,
           input [7:0] DIN,
           input irq,
           input nmi,
           output reg [7:0] dout, output reg [15:0] aout,
           output reg mr,
           output reg mw);
  reg [7:0] A, X, Y;
  reg [7:0] SP, T, P;
  reg [7:0] IR;
  reg [2:0] State;
  reg GotInterrupt;
  
  reg IsResetInterrupt;
  wire [15:0] PC;
  reg JumpTaken;
  wire JumpNoOverflow;

  // De-multiplex microcode
  wire [37:0] MicroCode;
  wire [1:0] LoadSP = MicroCode[1:0];            // 7 LUT
  wire [1:0] LoadPC = MicroCode[3:2];            // 12 LUT
  wire [1:0] AddrBus = MicroCode[5:4];           // 18 LUT
  wire [2:0] MemWrite = MicroCode[8:6];          // 10 LUT
  wire [4:0] AddrCtrl = MicroCode[13:9];       
  wire       FlagCtrl = MicroCode[14];           // RegWrite + FlagCtrl = 22 LUT
  wire [1:0] LoadT = MicroCode[16:15];           // 13 LUT
  wire [1:0] StateCtrl = MicroCode[18:17];
  wire [2:0] FlagsCtrl = MicroCode[21:19];
  wire [15:0] IrFlags = MicroCode[37:22];

  // Load Instruction Register? Force BRK on Interrupt.
  wire [7:0] NextIR = (State == 0) ? (GotInterrupt ? 8'd0 : DIN) : IR;
  wire IsBranchCycle1 = (IR[4:0] == 5'b10000) && State[0];

  // Compute next state.
  reg [2:0] NextState;
  always begin
    case (StateCtrl)
    0: NextState = State + 3'd1;
    1: NextState = (AXCarry ? 3'd4 : 3'd5);
    2: NextState = (IsBranchCycle1 && JumpTaken) ? 2 : 0; // Override next state if the branch is taken.
    3: NextState = (JumpNoOverflow ? 3'd0 : 3'd4);
    endcase
  end

  wire [15:0] AX;
  wire AXCarry;
AddressGenerator addgen(clk, ce, AddrCtrl, {IrFlags[0], IrFlags[1]}, DIN, T, X, Y, AX, AXCarry);

// Microcode table has a 1 clock latency (block ram).
MicroCodeTable micro2(clk, ce, reset, NextIR, NextState, MicroCode);

  wire [7:0] AluR;
  wire [7:0] AluIntR;
  wire CO, VO, SO,ZO;
NewAlu new_alu(IrFlags[15:5], A,X,Y,SP,DIN,T, P[0], P[6], CO, VO, SO, ZO, AluR, AluIntR);

// Registers
always @(posedge clk or posedge reset) if (reset) begin
  A <= 0;
  X <= 0;
  Y <= 0;
end else if (ce) begin
  if (FlagCtrl & IrFlags[2]) X <= AluR;
  if (FlagCtrl & IrFlags[3]) A <= AluR;
  if (FlagCtrl & IrFlags[4]) Y <= AluR;
end

// Program counter
ProgramCounter pc(clk, ce, LoadPC, GotInterrupt, DIN, T, PC, JumpNoOverflow);

reg IsNMIInterrupt;
reg LastNMI;
// NMI is triggered at any time, except during reset, or when we're in the middle of
// reading the vector address
wire turn_nmi_on = (AddrBus != 3) && !IsResetInterrupt && nmi && !LastNMI;
// Controls whether we'll remember the state in LastNMI
wire nmi_remembered = (AddrBus != 3) && !IsResetInterrupt ? nmi : LastNMI;
// NMI flag is cleared right after we read the vector address
wire turn_nmi_off = (AddrBus == 3) && (State[0] == 0);
// Controls whether IsNmiInterrupt will get set
wire nmi_active = turn_nmi_on ? 1 : turn_nmi_off ? 0 : IsNMIInterrupt;
always @(posedge clk or posedge reset) begin
  if (reset) begin
    IsNMIInterrupt <= 0;
    LastNMI <= 0;
  end else if (ce) begin
    IsNMIInterrupt <= nmi_active;
    LastNMI <= nmi_remembered;
  end
end

// Generate outputs from module...
always begin
  dout = 8'bX;
  case (MemWrite[1:0])
  'b00: dout = T;
  'b01: dout = AluR;
  'b10: dout = {P[7:6], 1'b1, !GotInterrupt, P[3:0]};
  'b11: dout = State[0] ? PC[7:0] : PC[15:8];
  endcase
  mw = MemWrite[2] && !IsResetInterrupt; // Prevent writing while handling a reset
  mr = !mw;
end

always begin
  case (AddrBus)
  0: aout = PC;
  1: aout = AX;
  2: aout = {8'h01, SP};
  // irq/BRK vector FFFE
  // nmi vector FFFA
  // Reset vector FFFC
  3: aout = {13'b1111_1111_1111_1, !IsNMIInterrupt, !IsResetInterrupt, ~State[0]};
  endcase 
end

 
always @(posedge clk) begin
  if (reset) begin
    // Reset runs the BRK instruction as usual.
    State <= 0;
    IR <= 0;
    GotInterrupt <= 1;
    IsResetInterrupt <= 1;
    P <= 'h24;
    SP <= 0;
    T <= 0;
    JumpTaken <= 0;
  end else if (ce) begin      
    // Stack pointer control.
    // The operand is an optimization that either
    // returns -1,0,1 depending on LoadSP 
    case (LoadSP)
    0,2,3: SP <= SP + { {7{LoadSP[0]}}, LoadSP[1] };
    1: SP <= X;
    endcase 

    // LoadT control
    case (LoadT)
    2: T <= DIN;
    3: T <= AluIntR;
    endcase

    if (FlagCtrl) begin
      case(FlagsCtrl)
      0: P <= P;      // No Op
      1: {P[0], P[1], P[6], P[7]} <= {CO, ZO, VO, SO}; // ALU
      2: P[2] <= 1;     // BRK
      3: P[6] <= 0;     // CLV
      4: {P[7:6],P[3:0]} <= {DIN[7:6], DIN[3:0]}; // RTI/PLP
      5: P[0] <= IR[5]; // CLC/SEC
      6: P[2] <= IR[5]; // CLI/SEI
      7: P[3] <= IR[5]; // CLD/SED
      endcase
    end

    // Compute if the jump is to be taken. Result is stored in a flipflop, so
    // it won't be available until next cycle.
    // NOTE: Using DIN here. DIN is IR at cycle 0. This means JumpTaken will
    // contain the Jump status at cycle 1.
    case (DIN[7:5])
    0: JumpTaken <= ~P[7]; // BPL
    1: JumpTaken <=  P[7]; // BMI
    2: JumpTaken <= ~P[6]; // BVC
    3: JumpTaken <=  P[6]; // BVS
    4: JumpTaken <= ~P[0]; // BCC
    5: JumpTaken <=  P[0]; // BCS
    6: JumpTaken <= ~P[1]; // BNE
    7: JumpTaken <=  P[1]; // BEQ
    endcase
    
    // Check the interrupt status on the last cycle of the current instruction,
    // (or on cycle #1 of any branch instruction)
    if (StateCtrl == 2'b10) begin
      GotInterrupt <= (irq & ~P[2]) | nmi_active;
      IsResetInterrupt <= 0;
    end

    IR <= NextIR;
    State <= NextState;
  end
end
endmodule
// Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.
 
module LenCtr_Lookup(input [4:0] X, output [7:0] Yout);
reg [6:0] Y;
always @*
begin
  case(X)
  0: Y = 7'h05;
  1: Y = 7'h7F;
  2: Y = 7'h0A;
  3: Y = 7'h01;
  4: Y = 7'h14;
  5: Y = 7'h02;
  6: Y = 7'h28;
  7: Y = 7'h03;
  8: Y = 7'h50;
  9: Y = 7'h04;
  10: Y = 7'h1E;
  11: Y = 7'h05;
  12: Y = 7'h07;
  13: Y = 7'h06;
  14: Y = 7'h0D;
  15: Y = 7'h07;
  16: Y = 7'h06;
  17: Y = 7'h08;
  18: Y = 7'h0C;
  19: Y = 7'h09;
  20: Y = 7'h18;
  21: Y = 7'h0A;
  22: Y = 7'h30;
  23: Y = 7'h0B;
  24: Y = 7'h60;
  25: Y = 7'h0C;
  26: Y = 7'h24;
  27: Y = 7'h0D;
  28: Y = 7'h08;
  29: Y = 7'h0E;
  30: Y = 7'h10;
  31: Y = 7'h0F;
  endcase
end
assign Yout = {Y, 1'b0};
endmodule

module SquareChan(input clk, input ce, input reset, input sq2,
                  input [1:0] Addr,
                  input [7:0] DIN,
                  input MW,
                  input LenCtr_Clock,
                  input Env_Clock,
                  input Enabled,
                  input [7:0] LenCtr_In,
                  output reg [3:0] Sample,
                  output IsNonZero);
reg [7:0] LenCtr;

// Register 1
reg [1:0] Duty;
reg EnvLoop, EnvDisable, EnvDoReset;
reg [3:0] Volume, Envelope, EnvDivider;
wire LenCtrHalt = EnvLoop; // Aliased bit
assign IsNonZero = (LenCtr != 0);
// Register 2
reg SweepEnable, SweepNegate, SweepReset;
reg [2:0] SweepPeriod, SweepDivider, SweepShift;

reg [10:0] Period;
reg [11:0] TimerCtr;
reg [2:0] SeqPos;
wire [10:0] ShiftedPeriod = (Period >> SweepShift);
wire [10:0] PeriodRhs = (SweepNegate ? (~ShiftedPeriod + {10'b0, sq2}) : ShiftedPeriod);
wire [11:0] NewSweepPeriod = Period + PeriodRhs;
wire ValidFreq = Period[10:3] >= 8 && (SweepNegate || !NewSweepPeriod[11]);

always @(posedge clk) if (reset) begin
    LenCtr <= 0;
    Duty <= 0;
    EnvDoReset <= 0;
    EnvLoop <= 0;
    EnvDisable <= 0;
    Volume <= 0;
    Envelope <= 0;
    EnvDivider <= 0;
    SweepEnable <= 0;
    SweepNegate <= 0;
    SweepReset <= 0;
    SweepPeriod <= 0;
    SweepDivider <= 0;
    SweepShift <= 0;    
    Period <= 0;
    TimerCtr <= 0;
    SeqPos <= 0;
  end else if (ce) begin
  // Check if writing to the regs of this channel
  // NOTE: This needs to be done before the clocking below.
  if (MW) begin
    case(Addr)
    0: begin
//      if (sq2) $write("SQ0: Duty=%d, EnvLoop=%d, EnvDisable=%d, Volume=%d\n", DIN[7:6], DIN[5], DIN[4], DIN[3:0]);
      Duty <= DIN[7:6];
      EnvLoop <= DIN[5];
      EnvDisable <= DIN[4];
      Volume <= DIN[3:0];
    end
    1: begin
//      if (sq2) $write("SQ1: SweepEnable=%d, SweepPeriod=%d, SweepNegate=%d, SweepShift=%d, DIN=%X\n", DIN[7], DIN[6:4], DIN[3], DIN[2:0], DIN);
      SweepEnable <= DIN[7];
      SweepPeriod <= DIN[6:4];
      SweepNegate <= DIN[3];
      SweepShift <= DIN[2:0];
      SweepReset <= 1;
    end
    2: begin
//      if (sq2) $write("SQ2: Period=%d. DIN=%X\n", DIN, DIN);
      Period[7:0] <= DIN;
    end
    3: begin
      // Upper bits of the period
//      if (sq2) $write("SQ3: PeriodUpper=%d LenCtr=%x DIN=%X\n", DIN[2:0], LenCtr_In, DIN);
      Period[10:8] <= DIN[2:0];
      LenCtr <= LenCtr_In;
      EnvDoReset <= 1;
      SeqPos <= 0;
    end
    endcase
  end

  
  // Count down the square timer...
  if (TimerCtr == 0) begin
    // Timer was clocked
    TimerCtr <= {Period, 1'b0};
    SeqPos <= SeqPos - 1;
  end else begin
    TimerCtr <= TimerCtr - 1;
  end

  // Clock the length counter?
  if (LenCtr_Clock && LenCtr != 0 && !LenCtrHalt) begin
    LenCtr <= LenCtr - 1;
  end
  
  // Clock the sweep unit?
  if (LenCtr_Clock) begin
    if (SweepDivider == 0) begin
      SweepDivider <= SweepPeriod;
      if (SweepEnable && SweepShift != 0 && ValidFreq)
        Period <= NewSweepPeriod[10:0];
    end else begin
      SweepDivider <= SweepDivider - 1;
    end
    if (SweepReset)
      SweepDivider <= SweepPeriod;
    SweepReset <= 0;
  end
  
  // Clock the envelope generator?
  if (Env_Clock) begin
    if (EnvDoReset) begin
      EnvDivider <= Volume;
      Envelope <= 15;
      EnvDoReset <= 0;
    end else if (EnvDivider == 0) begin
      EnvDivider <= Volume;
      if (Envelope != 0 || EnvLoop)
        Envelope <= Envelope - 1;
    end else begin
      EnvDivider <= EnvDivider - 1;
    end
  end
 
  // Length counter forced to zero if disabled.
  if (!Enabled)
    LenCtr <= 0;
end

reg DutyEnabled;  
always @* begin
  // Determine if the duty is enabled or not
  case (Duty)
  0: DutyEnabled = (SeqPos == 7);
  1: DutyEnabled = (SeqPos >= 6);
  2: DutyEnabled = (SeqPos >= 4);
  3: DutyEnabled = (SeqPos < 6);
  endcase

  // Compute the output
  if (LenCtr == 0 || !ValidFreq || !DutyEnabled)
    Sample = 0;
  else
    Sample = EnvDisable ? Volume : Envelope;
end
endmodule



module TriangleChan(input clk, input ce, input reset,
                    input [1:0] Addr,
                    input [7:0] DIN,
                    input MW,
                    input LenCtr_Clock,
                    input LinCtr_Clock,
                    input Enabled,
                    input [7:0] LenCtr_In,
                    output [3:0] Sample,
                    output IsNonZero);
  //
  reg [10:0] Period, TimerCtr;
  reg [4:0] SeqPos;
  //
  // Linear counter state
  reg [6:0] LinCtrPeriod, LinCtr;
  reg LinCtrl, LinHalt;
  wire LinCtrZero = (LinCtr == 0);
  //
  // Length counter state
  reg [7:0] LenCtr;
  wire LenCtrHalt = LinCtrl; // Aliased bit
  wire LenCtrZero = (LenCtr == 0);
  assign IsNonZero = !LenCtrZero;
  //
  always @(posedge clk) if (reset) begin
    Period <= 0;
    TimerCtr <= 0;
    SeqPos <= 0;
    LinCtrPeriod <= 0;
    LinCtr <= 0;
    LinCtrl <= 0;
    LinHalt <= 0;
    LenCtr <= 0;
  end else if (ce) begin
    // Check if writing to the regs of this channel 
    if (MW) begin
      case (Addr)
      0: begin
        LinCtrl <= DIN[7];
        LinCtrPeriod <= DIN[6:0];
      end
      2: begin
        Period[7:0] <= DIN;
      end
      3: begin
        Period[10:8] <= DIN[2:0];
        LenCtr <= LenCtr_In;
        LinHalt <= 1;
      end
      endcase
    end

    // Count down the period timer...
    if (TimerCtr == 0) begin
      TimerCtr <= Period;
    end else begin
      TimerCtr <= TimerCtr - 1;
    end
    //
    // Clock the length counter?
    if (LenCtr_Clock && !LenCtrZero && !LenCtrHalt) begin
      LenCtr <= LenCtr - 1;
    end
    //
    // Clock the linear counter?
    if (LinCtr_Clock) begin
      if (LinHalt)
        LinCtr <= LinCtrPeriod;
      else if (!LinCtrZero)
        LinCtr <= LinCtr - 1;
      if (!LinCtrl)
        LinHalt <= 0;
    end
    //
    // Length counter forced to zero if disabled.
    if (!Enabled)
      LenCtr <= 0;
      //
    // Clock the sequencer position
    if (TimerCtr == 0 && !LenCtrZero && !LinCtrZero)
      SeqPos <= SeqPos + 1;
  end
  // Generate the output
  assign Sample = SeqPos[3:0] ^ {4{~SeqPos[4]}};
  //
endmodule


module NoiseChan(input clk, input ce, input reset,
                 input [1:0] Addr,
                 input [7:0] DIN,
                 input MW,
                 input LenCtr_Clock,
                 input Env_Clock,
                 input Enabled,
                 input [7:0] LenCtr_In,
                 output [3:0] Sample,
                 output IsNonZero);
  //
  // Envelope volume
  reg EnvLoop, EnvDisable, EnvDoReset;
  reg [3:0] Volume, Envelope, EnvDivider;
  // Length counter
  wire LenCtrHalt = EnvLoop; // Aliased bit
  reg [7:0] LenCtr;
  //
  reg ShortMode;
  reg [14:0] Shift = 1;
  
  assign IsNonZero = (LenCtr != 0);
  //
  // Period stuff
  reg [3:0] Period;
  reg [11:0] NoisePeriod, TimerCtr;
  always @* begin
    case (Period)
    0: NoisePeriod = 12'h004;
    1: NoisePeriod = 12'h008;
    2: NoisePeriod = 12'h010;
    3: NoisePeriod = 12'h020;
    4: NoisePeriod = 12'h040;
    5: NoisePeriod = 12'h060;
    6: NoisePeriod = 12'h080;
    7: NoisePeriod = 12'h0A0;
    8: NoisePeriod = 12'h0CA;
    9: NoisePeriod = 12'h0FE;
    10: NoisePeriod = 12'h17C;
    11: NoisePeriod = 12'h1FC;
    12: NoisePeriod = 12'h2FA;
    13: NoisePeriod = 12'h3F8;
    14: NoisePeriod = 12'h7F2;
    15: NoisePeriod = 12'hFE4;  
    endcase
  end
  //
  always @(posedge clk) if (reset) begin
    EnvLoop <= 0;
    EnvDisable <= 0;
    EnvDoReset <= 0;
    Volume <= 0;
    Envelope <= 0;
    EnvDivider <= 0;
    LenCtr <= 0;
    ShortMode <= 0;
    Shift <= 1;
    Period <= 0;
    TimerCtr <= 0;
  end else if (ce) begin
    // Check if writing to the regs of this channel 
    if (MW) begin
      case (Addr)
      0: begin
        EnvLoop <= DIN[5];
        EnvDisable <= DIN[4];
        Volume <= DIN[3:0];
      end
      2: begin
        ShortMode <= DIN[7];
        Period <= DIN[3:0];
      end
      3: begin
        LenCtr <= LenCtr_In;
        EnvDoReset <= 1;
      end
      endcase
    end
    // Count down the period timer...
    if (TimerCtr == 0) begin
      TimerCtr <= NoisePeriod;
      // Clock the shift register. Use either 
      // bit 1 or 6 as the tap.
      Shift <= { 
        Shift[0] ^ (ShortMode ? Shift[6] : Shift[1]), 
        Shift[14:1]}; 
    end else begin
      TimerCtr <= TimerCtr - 1;
    end
    // Clock the length counter?
    if (LenCtr_Clock && LenCtr != 0 && !LenCtrHalt) begin
      LenCtr <= LenCtr - 1;
    end
    // Clock the envelope generator?
    if (Env_Clock) begin
      if (EnvDoReset) begin
        EnvDivider <= Volume;
        Envelope <= 15;
        EnvDoReset <= 0;
      end else if (EnvDivider == 0) begin
        EnvDivider <= Volume;
        if (Envelope != 0)
          Envelope <= Envelope - 1;
        else if (EnvLoop)
          Envelope <= 15;
      end else
        EnvDivider <= EnvDivider - 1;
    end
    if (!Enabled)
      LenCtr <= 0;
  end
  // Produce the output signal
  assign Sample = 
    (LenCtr == 0 || Shift[0]) ?
      0 : 
      (EnvDisable ? Volume : Envelope);
endmodule

module DmcChan(input clk, input ce, input reset,
               input odd_or_even,
               input [2:0] Addr,
               input [7:0] DIN,
               input MW,
               output [6:0] Sample,
               output DmaReq,          // 1 when DMC wants DMA
               input DmaAck,           // 1 when DMC byte is on DmcData. DmcDmaRequested should go low.
               output [15:0] DmaAddr,  // Address DMC wants to read
               input [7:0] DmaData,    // Input data to DMC from memory.
               output Irq,
               output IsDmcActive);
  reg IrqEnable;
  reg IrqActive;
  reg Loop;                 // Looping enabled
  reg [3:0] Freq;           // Current value of frequency register
  reg [6:0] Dac = 0;        // Current value of DAC
  reg [7:0] SampleAddress;  // Base address of sample
  reg [7:0] SampleLen;      // Length of sample
  reg [7:0] ShiftReg;       // Shift register
  reg [8:0] Cycles;         // Down counter, is the period
  reg [14:0] Address;        // 15 bits current address, 0x8000-0xffff
  reg [11:0] BytesLeft;      // 12 bits bytes left counter 0 - 4081.
  reg [2:0] BitsUsed;        // Number of bits left in the SampleBuffer.
  reg [7:0] SampleBuffer;    // Next value to be loaded into shift reg
  reg HasSampleBuffer;       // Sample buffer is nonempty
  reg HasShiftReg;           // Shift reg is non empty
  reg [8:0] NewPeriod[0:15];
  reg DmcEnabled;
  reg [1:0] ActivationDelay;
  assign DmaAddr = {1'b1, Address};
  assign Sample = Dac;
  assign Irq = IrqActive;
  assign IsDmcActive = DmcEnabled;
  
  assign DmaReq = !HasSampleBuffer && DmcEnabled && !ActivationDelay[0];
    
  initial begin
    NewPeriod[0] = 428;
    NewPeriod[1] = 380;
    NewPeriod[2] = 340;
    NewPeriod[3] = 320;
    NewPeriod[4] = 286;
    NewPeriod[5] = 254;
    NewPeriod[6] = 226;
    NewPeriod[7] = 214;
    NewPeriod[8] = 190;
    NewPeriod[9] = 160;
    NewPeriod[10] = 142;
    NewPeriod[11] = 128;
    NewPeriod[12] = 106;
    NewPeriod[13] = 84;
    NewPeriod[14] = 72;
    NewPeriod[15] = 54;
  end
  // Shift register initially loaded with 07
  always @(posedge clk) begin
    if (reset) begin
      IrqEnable <= 0;
      IrqActive <= 0;
      Loop <= 0;
      Freq <= 0;
      Dac <= 0;
      SampleAddress <= 0;
      SampleLen <= 0;
      ShiftReg <= 8'hff;
      Cycles <= 439;
      Address <= 0;
      BytesLeft <= 0;
      BitsUsed <= 0;
      SampleBuffer <= 0;
      HasSampleBuffer <= 0;
      HasShiftReg <= 0;
      DmcEnabled <= 0;
      ActivationDelay <= 0;
    end else if (ce) begin
      if (ActivationDelay == 3 && !odd_or_even) ActivationDelay <= 1;
      if (ActivationDelay == 1) ActivationDelay <= 0;
      
      if (MW) begin
        case (Addr)
        0: begin  // $4010   il-- ffff   IRQ enable, loop, frequency index
            IrqEnable <= DIN[7];
            Loop <= DIN[6];
            Freq <= DIN[3:0];
            if (!DIN[7]) IrqActive <= 0;
          end
        1: begin  // $4011   -ddd dddd   DAC
            // This will get missed if the Dac <= far below runs, that is by design.
            Dac <= DIN[6:0];
          end
        2: begin  // $4012   aaaa aaaa   sample address
            SampleAddress <= DIN[7:0];
          end
        3: begin  // $4013   llll llll   sample length
            SampleLen <= DIN[7:0];
          end
        5: begin // $4015 write	---D NT21  Enable DMC (D)
            IrqActive <= 0;
            DmcEnabled <= DIN[4];
            // If the DMC bit is set, the DMC sample will be restarted only if not already active.
            if (DIN[4] && !DmcEnabled) begin
              Address <= {1'b1, SampleAddress, 6'b000000};
              BytesLeft <= {SampleLen, 4'b0000};
              ActivationDelay <= 3;
            end
          end
        endcase
      end

      Cycles <= Cycles - 1;
      if (Cycles == 1) begin
        Cycles <= NewPeriod[Freq];
        if (HasShiftReg) begin
          if (ShiftReg[0]) begin
            Dac[6:1] <= (Dac[6:1] != 6'b111111) ? Dac[6:1] + 6'b000001 : Dac[6:1];
          end else begin
            Dac[6:1] <= (Dac[6:1] != 6'b000000) ? Dac[6:1] + 6'b111111 : Dac[6:1];
          end
        end
        ShiftReg <= {1'b0, ShiftReg[7:1]};
        BitsUsed <= BitsUsed + 1;
        if (BitsUsed == 7) begin
          HasShiftReg <= HasSampleBuffer;
          ShiftReg <= SampleBuffer;
          HasSampleBuffer <= 0;
        end
      end
      
      // Acknowledge DMA?
      if (DmaAck) begin
        Address <= Address + 1;
        BytesLeft <= BytesLeft - 1;
        HasSampleBuffer <= 1;
        SampleBuffer <= DmaData;
        if (BytesLeft == 0) begin
          Address <= {1'b1, SampleAddress, 6'b000000};
          BytesLeft <= {SampleLen, 4'b0000};
          DmcEnabled <= Loop;
          if (!Loop && IrqEnable)
            IrqActive <= 1;
        end
      end      
    end
  end
endmodule

module ApuLookupTable(input clk, input [7:0] in_a, input [7:0] in_b, output [15:0] out);
  reg [15:0] lookup[0:511];
  reg [15:0] tmp_a, tmp_b;
  initial begin
    lookup[  0] =     0; lookup[  1] =   760; lookup[  2] =  1503; lookup[  3] =  2228;
    lookup[  4] =  2936; lookup[  5] =  3627; lookup[  6] =  4303; lookup[  7] =  4963;
    lookup[  8] =  5609; lookup[  9] =  6240; lookup[ 10] =  6858; lookup[ 11] =  7462;
    lookup[ 12] =  8053; lookup[ 13] =  8631; lookup[ 14] =  9198; lookup[ 15] =  9752;
    lookup[ 16] = 10296; lookup[ 17] = 10828; lookup[ 18] = 11349; lookup[ 19] = 11860;
    lookup[ 20] = 12361; lookup[ 21] = 12852; lookup[ 22] = 13334; lookup[ 23] = 13807;
    lookup[ 24] = 14270; lookup[ 25] = 14725; lookup[ 26] = 15171; lookup[ 27] = 15609;
    lookup[ 28] = 16039; lookup[ 29] = 16461; lookup[ 30] = 16876; lookup[256] =     0;
    lookup[257] =   439; lookup[258] =   874; lookup[259] =  1306; lookup[260] =  1735;
    lookup[261] =  2160; lookup[262] =  2581; lookup[263] =  2999; lookup[264] =  3414;
    lookup[265] =  3826; lookup[266] =  4234; lookup[267] =  4639; lookup[268] =  5041;
    lookup[269] =  5440; lookup[270] =  5836; lookup[271] =  6229; lookup[272] =  6618;
    lookup[273] =  7005; lookup[274] =  7389; lookup[275] =  7769; lookup[276] =  8147;
    lookup[277] =  8522; lookup[278] =  8895; lookup[279] =  9264; lookup[280] =  9631;
    lookup[281] =  9995; lookup[282] = 10356; lookup[283] = 10714; lookup[284] = 11070;
    lookup[285] = 11423; lookup[286] = 11774; lookup[287] = 12122; lookup[288] = 12468;
    lookup[289] = 12811; lookup[290] = 13152; lookup[291] = 13490; lookup[292] = 13825;
    lookup[293] = 14159; lookup[294] = 14490; lookup[295] = 14818; lookup[296] = 15145;
    lookup[297] = 15469; lookup[298] = 15791; lookup[299] = 16110; lookup[300] = 16427;
    lookup[301] = 16742; lookup[302] = 17055; lookup[303] = 17366; lookup[304] = 17675;
    lookup[305] = 17981; lookup[306] = 18286; lookup[307] = 18588; lookup[308] = 18888;
    lookup[309] = 19187; lookup[310] = 19483; lookup[311] = 19777; lookup[312] = 20069;
    lookup[313] = 20360; lookup[314] = 20648; lookup[315] = 20935; lookup[316] = 21219;
    lookup[317] = 21502; lookup[318] = 21783; lookup[319] = 22062; lookup[320] = 22339;
    lookup[321] = 22615; lookup[322] = 22889; lookup[323] = 23160; lookup[324] = 23431;
    lookup[325] = 23699; lookup[326] = 23966; lookup[327] = 24231; lookup[328] = 24494;
    lookup[329] = 24756; lookup[330] = 25016; lookup[331] = 25274; lookup[332] = 25531;
    lookup[333] = 25786; lookup[334] = 26040; lookup[335] = 26292; lookup[336] = 26542;
    lookup[337] = 26791; lookup[338] = 27039; lookup[339] = 27284; lookup[340] = 27529;
    lookup[341] = 27772; lookup[342] = 28013; lookup[343] = 28253; lookup[344] = 28492;
    lookup[345] = 28729; lookup[346] = 28964; lookup[347] = 29198; lookup[348] = 29431;
    lookup[349] = 29663; lookup[350] = 29893; lookup[351] = 30121; lookup[352] = 30349;
    lookup[353] = 30575; lookup[354] = 30800; lookup[355] = 31023; lookup[356] = 31245;
    lookup[357] = 31466; lookup[358] = 31685; lookup[359] = 31904; lookup[360] = 32121;
    lookup[361] = 32336; lookup[362] = 32551; lookup[363] = 32764; lookup[364] = 32976;
    lookup[365] = 33187; lookup[366] = 33397; lookup[367] = 33605; lookup[368] = 33813;
    lookup[369] = 34019; lookup[370] = 34224; lookup[371] = 34428; lookup[372] = 34630;
    lookup[373] = 34832; lookup[374] = 35032; lookup[375] = 35232; lookup[376] = 35430;
    lookup[377] = 35627; lookup[378] = 35823; lookup[379] = 36018; lookup[380] = 36212;
    lookup[381] = 36405; lookup[382] = 36597; lookup[383] = 36788; lookup[384] = 36978;
    lookup[385] = 37166; lookup[386] = 37354; lookup[387] = 37541; lookup[388] = 37727;
    lookup[389] = 37912; lookup[390] = 38095; lookup[391] = 38278; lookup[392] = 38460;
    lookup[393] = 38641; lookup[394] = 38821; lookup[395] = 39000; lookup[396] = 39178;
    lookup[397] = 39355; lookup[398] = 39532; lookup[399] = 39707; lookup[400] = 39881;
    lookup[401] = 40055; lookup[402] = 40228; lookup[403] = 40399; lookup[404] = 40570;
    lookup[405] = 40740; lookup[406] = 40909; lookup[407] = 41078; lookup[408] = 41245;
    lookup[409] = 41412; lookup[410] = 41577; lookup[411] = 41742; lookup[412] = 41906;
    lookup[413] = 42070; lookup[414] = 42232; lookup[415] = 42394; lookup[416] = 42555;
    lookup[417] = 42715; lookup[418] = 42874; lookup[419] = 43032; lookup[420] = 43190;
    lookup[421] = 43347; lookup[422] = 43503; lookup[423] = 43659; lookup[424] = 43813;
    lookup[425] = 43967; lookup[426] = 44120; lookup[427] = 44273; lookup[428] = 44424;
    lookup[429] = 44575; lookup[430] = 44726; lookup[431] = 44875; lookup[432] = 45024;
    lookup[433] = 45172; lookup[434] = 45319; lookup[435] = 45466; lookup[436] = 45612;
    lookup[437] = 45757; lookup[438] = 45902; lookup[439] = 46046; lookup[440] = 46189;
    lookup[441] = 46332; lookup[442] = 46474; lookup[443] = 46615; lookup[444] = 46756;
    lookup[445] = 46895; lookup[446] = 47035; lookup[447] = 47173; lookup[448] = 47312;
    lookup[449] = 47449; lookup[450] = 47586; lookup[451] = 47722; lookup[452] = 47857;
    lookup[453] = 47992; lookup[454] = 48127; lookup[455] = 48260; lookup[456] = 48393;
    lookup[457] = 48526; lookup[458] = 48658;  
  end
  always @(posedge clk) begin
    tmp_a <= lookup[{1'b0, in_a}];
    tmp_b <= lookup[{1'b1, in_b}];
  end
  assign out = tmp_a + tmp_b;
endmodule


module APU(input clk, input ce, input reset,
           input [4:0] ADDR,  // APU Address Line
           input [7:0] DIN,   // Data to APU
           output [7:0] DOUT, // Data from APU
           input MW,          // Writes to APU
           input MR,          // Reads from APU
           input [4:0] audio_channels, // Enabled audio channels
           output [15:0] Sample,

           output DmaReq,      // 1 when DMC wants DMA
           input DmaAck,           // 1 when DMC byte is on DmcData. DmcDmaRequested should go low.
           output [15:0] DmaAddr,  // Address DMC wants to read
           input [7:0] DmaData,    // Input data to DMC from memory.

           output odd_or_even,
           output IRQ);       // IRQ asserted

// Which channels are enabled?
reg [3:0] Enabled;

// Output samples from the 4 channels
wire [3:0] Sq1Sample,Sq2Sample,TriSample,NoiSample;

// Output samples from the DMC channel
wire [6:0] DmcSample;
wire DmcIrq;
wire IsDmcActive;

// Generate internal memory write signals
wire ApuMW0 = MW && ADDR[4:2]==0; // SQ1
wire ApuMW1 = MW && ADDR[4:2]==1; // SQ2
wire ApuMW2 = MW && ADDR[4:2]==2; // TRI
wire ApuMW3 = MW && ADDR[4:2]==3; // NOI
wire ApuMW4 = MW && ADDR[4:2]>=4; // DMC
wire ApuMW5 = MW && ADDR[4:2]==5; // Control registers

wire Sq1NonZero, Sq2NonZero, TriNonZero, NoiNonZero;

// Common input to all channels
wire [7:0] LenCtr_In;
LenCtr_Lookup len(DIN[7:3], LenCtr_In);


// Frame sequencer registers
reg FrameSeqMode;
reg [15:0] Cycles;
reg ClkE, ClkL;
reg Wrote4017;
reg [1:0] IrqCtr;
reg InternalClock; // APU Differentiates between Even or Odd clocks
assign odd_or_even = InternalClock;


// Generate each channel
SquareChan   Sq1(clk, ce, reset, 0, ADDR[1:0], DIN, ApuMW0, ClkL, ClkE, Enabled[0], LenCtr_In, Sq1Sample, Sq1NonZero);
SquareChan   Sq2(clk, ce, reset, 1, ADDR[1:0], DIN, ApuMW1, ClkL, ClkE, Enabled[1], LenCtr_In, Sq2Sample, Sq2NonZero);
TriangleChan Tri(clk, ce, reset, ADDR[1:0], DIN, ApuMW2, ClkL, ClkE, Enabled[2], LenCtr_In, TriSample, TriNonZero);
NoiseChan    Noi(clk, ce, reset, ADDR[1:0], DIN, ApuMW3, ClkL, ClkE, Enabled[3], LenCtr_In, NoiSample, NoiNonZero);
DmcChan      Dmc(clk, ce, reset, odd_or_even, ADDR[2:0], DIN, ApuMW4, DmcSample, DmaReq, DmaAck, DmaAddr, DmaData, DmcIrq, IsDmcActive);

// Reading this register clears the frame interrupt flag (but not the DMC interrupt flag).
// If an interrupt flag was set at the same moment of the read, it will read back as 1 but it will not be cleared.
reg FrameInterrupt, DisableFrameInterrupt;


//mode 0: 4-step  effective rate (approx)
//---------------------------------------
//    - - - f      60 Hz
//    - l - l     120 Hz
//    e e e e     240 Hz


//mode 1: 5-step  effective rate (approx)
//---------------------------------------
//    - - - - -   (interrupt flag never set)
//    l - l - -    96 Hz
//    e e e e -   192 Hz

   
always @(posedge clk) if (reset) begin
  FrameSeqMode <= 0;
  DisableFrameInterrupt <= 0;
  FrameInterrupt <= 0;
  Enabled <= 0;
  InternalClock <= 0;
  Wrote4017 <= 0;
  ClkE <= 0;
  ClkL <= 0;
  Cycles <= 4; // This needs to be 5 for proper power up behavior
  IrqCtr <= 0;
end else if (ce) begin   
  FrameInterrupt <= IrqCtr[1] ? 1 : (ADDR == 5'h15 && MR || ApuMW5 && ADDR[1:0] == 3 && DIN[6]) ? 0 : FrameInterrupt;
  InternalClock <= !InternalClock;
  IrqCtr <= {IrqCtr[0], 1'b0};
  Cycles <= Cycles + 1;
  ClkE <= 0;
  ClkL <= 0;
  if (Cycles == 7457) begin
    ClkE <= 1;
  end else if (Cycles == 14913) begin
    ClkE <= 1;
    ClkL <= 1;
    ClkE <= 1;
    ClkL <= 1;
  end else if (Cycles == 22371) begin
    ClkE <= 1;
  end else if (Cycles == 29829) begin
    if (!FrameSeqMode) begin
      ClkE <= 1;
      ClkL <= 1;
      Cycles <= 0;
      IrqCtr <= 3;
      FrameInterrupt <= 1;
    end
  end else if (Cycles == 37281) begin
    ClkE <= 1;
    ClkL <= 1;
    Cycles <= 0;
  end
  
  // Handle one cycle delayed write to 4017.
  Wrote4017 <= 0;
  if (Wrote4017) begin
    if (FrameSeqMode) begin
      ClkE <= 1;
      ClkL <= 1;
    end
    Cycles <= 0;
  end
  
//  if (ClkE||ClkL) $write("%d: Clocking %s%s\n", Cycles, ClkE?"E":" ", ClkL?"L":" ");

  // Handle writes to control registers
  if (ApuMW5) begin
    case (ADDR[1:0])
    1: begin // Register $4015
      Enabled <= DIN[3:0];
//      $write("$4015 = %X\n", DIN);
    end
    3: begin // Register $4017
      FrameSeqMode <= DIN[7]; // 1 = 5 frames cycle, 0 = 4 frames cycle
      DisableFrameInterrupt <= DIN[6];
     
      // If the internal clock is even, things happen
      // right away.
      if (!InternalClock) begin
        if (DIN[7]) begin
          ClkE <= 1;
          ClkL <= 1;
        end
        Cycles <= 0;
      end
      
      // Otherwise they get delayed one clock
      Wrote4017 <= InternalClock;
    end
    endcase
  end


end

ApuLookupTable lookup(clk, 
                      (audio_channels[0] ? {4'b0, Sq1Sample} : 8'b0) + 
                      (audio_channels[1] ? {4'b0, Sq2Sample} : 8'b0), 
                      (audio_channels[2] ? {4'b0, TriSample} + {3'b0, TriSample, 1'b0} : 8'b0) + 
                      (audio_channels[3] ? {3'b0, NoiSample, 1'b0} : 8'b0) +
                      (audio_channels[4] ? {1'b0, DmcSample} : 8'b0),
                      Sample);

wire frame_irq = FrameInterrupt && !DisableFrameInterrupt;

// Generate bus output
assign DOUT = {DmcIrq, frame_irq, 1'b0, 
               IsDmcActive,
               NoiNonZero,
               TriNonZero,
               Sq2NonZero,
               Sq1NonZero};

assign IRQ = frame_irq || DmcIrq;

endmodule
// Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.
module MUXCY(output O, input CI, input DI, input S);
  assign O = S ? CI : DI;
endmodule
module MUXCY_L(output LO, input CI, input DI, input S);
  assign LO = S ? CI : DI;
endmodule
module MUXCY_D(output LO, output O, input CI, input DI, input S);
  assign LO = S ? CI : DI;
  assign O = LO;
endmodule
module XORCY(output O, input CI, input LI);
  assign O = CI ^ LI;
endmodule
module XOR2(output O, input I0, input I1);
  assign O = I0 ^ I1;
endmodule// Simple, platform-agnostic single-ported RAM

module generic_ram(clock, reset, address, wren, write_data, read_data);

parameter integer WIDTH = 8;
parameter integer WORDS = 2048;
localparam ADDR_BITS = $clog2(WORDS-1);

input clock;
input reset;
input [ADDR_BITS-1:0] address;
input wren;
input [WIDTH-1:0] write_data;
output reg [WIDTH-1:0] read_data;

reg [WIDTH-1:0] mem[0:WORDS-1];

reg [ADDR_BITS-1:0] a_prereg;
reg [WIDTH-1:0] d_prereg;
reg wren_prereg;

always @(posedge clock) begin
  if (reset == 1'b1) begin
    wren_prereg <= 0;
    a_prereg <= 0;
    d_prereg <= 0;
  end else begin
    wren_prereg <= wren;
    a_prereg <= address;
    d_prereg <= write_data;
  end

  
  read_data <= mem[a_prereg];
  if (wren_prereg) mem[a_prereg] <= d_prereg;
end

endmodule// SPI flash memory interface, taken from the icosoc project

module icosoc_flashmem (
	input clk, reset,

	input valid,
	output reg ready,
	input [23:0] addr,
	output reg [31:0] rdata,

	output reg spi_cs,
	output reg spi_sclk,
	output reg spi_mosi,
	input spi_miso
);
	reg [7:0] buffer;
	reg [3:0] xfer_cnt;
	reg [3:0] state;

	always @(posedge clk) begin
		ready <= 0;
		if (reset || !valid || ready) begin
			spi_cs <= 1;
			spi_sclk <= 1;
			xfer_cnt <= 0;
			state <= 0;
		end else begin
			spi_cs <= 0;
			if (xfer_cnt) begin
				if (spi_sclk) begin
					spi_sclk <= 0;
					spi_mosi <= buffer[7];
				end else begin
					spi_sclk <= 1;
					buffer <= {buffer, spi_miso};
					xfer_cnt <= xfer_cnt - 1;
				end
			end else
			case (state)
				0: begin
					buffer <= 'h03;
					xfer_cnt <= 8;
					state <= 1;
				end
				1: begin
					buffer <= addr[23:16];
					xfer_cnt <= 8;
					state <= 2;
				end
				2: begin
					buffer <= addr[15:8];
					xfer_cnt <= 8;
					state <= 3;
				end
				3: begin
					buffer <= addr[7:0];
					xfer_cnt <= 8;
					state <= 4;
				end
				4: begin
					xfer_cnt <= 8;
					state <= 5;
				end
				5: begin
					rdata[7:0] <= buffer;
					xfer_cnt <= 8;
					state <= 6;
				end
				6: begin
					rdata[15:8] <= buffer;
					xfer_cnt <= 8;
					state <= 7;
				end
				7: begin
					rdata[23:16] <= buffer;
					xfer_cnt <= 8;
					state <= 8;
				end
				8: begin
					rdata[31:24] <= buffer;
					ready <= 1;
				end
			endcase
		end
	end
endmodule
module MicroCodeTableInner(input clk, input ce, input reset, input [7:0] IR, input [2:0] State, output reg [8:0] M);
  reg [8:0] L[0:2047];
  initial begin
L[0] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[2] = 9'b00_10_10100; // ['PCH->[SP--]', 'PCL->[SP--],', 'PCH->[SP--](KEEPAC)', 'PCL->[SP--](KEEPAC)']
L[3] = 9'b00_10_10100; // ['PCH->[SP--]', 'PCL->[SP--],', 'PCH->[SP--](KEEPAC)', 'PCL->[SP--](KEEPAC)']
L[4] = 9'b00_10_10101; // P->[SP--]
L[5] = 9'b00_11_00011; // [VECT]->T
L[6] = 9'b10_11_10011; // [VECT]:T->PC
L[7] = 9'bxx_xx_xxxxx; // []
L[8] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[9] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[10] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[11] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[12] = 9'b00_01_01011; // [AX]->AH,T->AL
L[13] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[14] = 9'bxx_xx_xxxxx; // []
L[15] = 9'bxx_xx_xxxxx; // []
L[16] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[17] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[18] = 9'bxx_xx_xxxxx; // []
L[19] = 9'bxx_xx_xxxxx; // []
L[20] = 9'bxx_xx_xxxxx; // []
L[21] = 9'bxx_xx_xxxxx; // []
L[22] = 9'bxx_xx_xxxxx; // []
L[23] = 9'bxx_xx_xxxxx; // []
L[24] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[25] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[26] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[27] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[28] = 9'b00_01_01011; // [AX]->AH,T->AL
L[29] = 9'b00_01_00011; // [AX]->T
L[30] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[31] = 9'b10_01_00101; // T->[AX]
L[32] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[33] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[34] = 9'bxx_xx_xxxxx; // []
L[35] = 9'bxx_xx_xxxxx; // []
L[36] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[37] = 9'bxx_xx_xxxxx; // []
L[38] = 9'bxx_xx_xxxxx; // []
L[39] = 9'bxx_xx_xxxxx; // []
L[40] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[41] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[42] = 9'bxx_xx_xxxxx; // []
L[43] = 9'bxx_xx_xxxxx; // []
L[44] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[45] = 9'bxx_xx_xxxxx; // []
L[46] = 9'bxx_xx_xxxxx; // []
L[47] = 9'bxx_xx_xxxxx; // []
L[48] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[49] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[50] = 9'bxx_xx_xxxxx; // []
L[51] = 9'bxx_xx_xxxxx; // []
L[52] = 9'b00_01_00011; // [AX]->T
L[53] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[54] = 9'b10_01_00101; // T->[AX]
L[55] = 9'bxx_xx_xxxxx; // []
L[56] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[57] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[58] = 9'bxx_xx_xxxxx; // []
L[59] = 9'bxx_xx_xxxxx; // []
L[60] = 9'b00_01_00011; // [AX]->T
L[61] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[62] = 9'b10_01_00101; // T->[AX]
L[63] = 9'bxx_xx_xxxxx; // []
L[64] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[65] = 9'b00_00_00011; // [PC]->
L[66] = 9'b10_10_01111; // P->[SP--]
L[67] = 9'bxx_xx_xxxxx; // []
L[68] = 9'bxx_xx_xxxxx; // []
L[69] = 9'bxx_xx_xxxxx; // []
L[70] = 9'bxx_xx_xxxxx; // []
L[71] = 9'bxx_xx_xxxxx; // []
L[72] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[73] = 9'b10_00_01101; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
L[74] = 9'bxx_xx_xxxxx; // []
L[75] = 9'bxx_xx_xxxxx; // []
L[76] = 9'bxx_xx_xxxxx; // []
L[77] = 9'bxx_xx_xxxxx; // []
L[78] = 9'bxx_xx_xxxxx; // []
L[79] = 9'bxx_xx_xxxxx; // []
L[80] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[81] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[82] = 9'bxx_xx_xxxxx; // []
L[83] = 9'bxx_xx_xxxxx; // []
L[84] = 9'bxx_xx_xxxxx; // []
L[85] = 9'bxx_xx_xxxxx; // []
L[86] = 9'bxx_xx_xxxxx; // []
L[87] = 9'bxx_xx_xxxxx; // []
L[88] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[89] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[90] = 9'bxx_xx_xxxxx; // []
L[91] = 9'bxx_xx_xxxxx; // []
L[92] = 9'bxx_xx_xxxxx; // []
L[93] = 9'bxx_xx_xxxxx; // []
L[94] = 9'bxx_xx_xxxxx; // []
L[95] = 9'bxx_xx_xxxxx; // []
L[96] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[97] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[98] = 9'b11_00_00001; // [PC++]->AH
L[99] = 9'bxx_xx_xxxxx; // []
L[100] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[101] = 9'bxx_xx_xxxxx; // []
L[102] = 9'bxx_xx_xxxxx; // []
L[103] = 9'bxx_xx_xxxxx; // []
L[104] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[105] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[106] = 9'b11_00_00001; // [PC++]->AH
L[107] = 9'bxx_xx_xxxxx; // []
L[108] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[109] = 9'bxx_xx_xxxxx; // []
L[110] = 9'bxx_xx_xxxxx; // []
L[111] = 9'bxx_xx_xxxxx; // []
L[112] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[113] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[114] = 9'b11_00_00001; // [PC++]->AH
L[115] = 9'bxx_xx_xxxxx; // []
L[116] = 9'b00_01_00011; // [AX]->T
L[117] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[118] = 9'b10_01_00101; // T->[AX]
L[119] = 9'bxx_xx_xxxxx; // []
L[120] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[121] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[122] = 9'b11_00_00001; // [PC++]->AH
L[123] = 9'bxx_xx_xxxxx; // []
L[124] = 9'b00_01_00011; // [AX]->T
L[125] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[126] = 9'b10_01_00101; // T->[AX]
L[127] = 9'bxx_xx_xxxxx; // []
L[128] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[129] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[130] = 9'b11_00_10001; // PC+T->PC
L[131] = 9'bxx_xx_xxxxx; // []
L[132] = 9'b10_00_00011; // ['NO-OP', '']
L[133] = 9'bxx_xx_xxxxx; // []
L[134] = 9'bxx_xx_xxxxx; // []
L[135] = 9'bxx_xx_xxxxx; // []
L[136] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[137] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[138] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[139] = 9'b01_01_01100; // [AX]->AH,T+Y->AL
L[140] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[141] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[142] = 9'bxx_xx_xxxxx; // []
L[143] = 9'bxx_xx_xxxxx; // []
L[144] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[145] = 9'b10_00_00011; // ['NO-OP', '']
L[146] = 9'bxx_xx_xxxxx; // []
L[147] = 9'bxx_xx_xxxxx; // []
L[148] = 9'bxx_xx_xxxxx; // []
L[149] = 9'bxx_xx_xxxxx; // []
L[150] = 9'bxx_xx_xxxxx; // []
L[151] = 9'bxx_xx_xxxxx; // []
L[152] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[153] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[154] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[155] = 9'b00_01_01100; // [AX]->AH,T+Y->AL
L[156] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[157] = 9'b00_01_00011; // [AX]->T
L[158] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[159] = 9'b10_01_00101; // T->[AX]
L[160] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[161] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[162] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[163] = 9'bxx_xx_xxxxx; // []
L[164] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[165] = 9'bxx_xx_xxxxx; // []
L[166] = 9'bxx_xx_xxxxx; // []
L[167] = 9'bxx_xx_xxxxx; // []
L[168] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[169] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[170] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[171] = 9'bxx_xx_xxxxx; // []
L[172] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[173] = 9'bxx_xx_xxxxx; // []
L[174] = 9'bxx_xx_xxxxx; // []
L[175] = 9'bxx_xx_xxxxx; // []
L[176] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[177] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[178] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[179] = 9'bxx_xx_xxxxx; // []
L[180] = 9'b00_01_00011; // [AX]->T
L[181] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[182] = 9'b10_01_00101; // T->[AX]
L[183] = 9'bxx_xx_xxxxx; // []
L[184] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[185] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[186] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[187] = 9'bxx_xx_xxxxx; // []
L[188] = 9'b00_01_00011; // [AX]->T
L[189] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[190] = 9'b10_01_00101; // T->[AX]
L[191] = 9'bxx_xx_xxxxx; // []
L[192] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[193] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[194] = 9'bxx_xx_xxxxx; // []
L[195] = 9'bxx_xx_xxxxx; // []
L[196] = 9'bxx_xx_xxxxx; // []
L[197] = 9'bxx_xx_xxxxx; // []
L[198] = 9'bxx_xx_xxxxx; // []
L[199] = 9'bxx_xx_xxxxx; // []
L[200] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[201] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[202] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[203] = 9'bxx_xx_xxxxx; // []
L[204] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[205] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[206] = 9'bxx_xx_xxxxx; // []
L[207] = 9'bxx_xx_xxxxx; // []
L[208] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[209] = 9'b10_00_00011; // ['NO-OP', '']
L[210] = 9'bxx_xx_xxxxx; // []
L[211] = 9'bxx_xx_xxxxx; // []
L[212] = 9'bxx_xx_xxxxx; // []
L[213] = 9'bxx_xx_xxxxx; // []
L[214] = 9'bxx_xx_xxxxx; // []
L[215] = 9'bxx_xx_xxxxx; // []
L[216] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[217] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[218] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[219] = 9'bxx_xx_xxxxx; // []
L[220] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[221] = 9'b00_01_00011; // [AX]->T
L[222] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[223] = 9'b10_01_00101; // T->[AX]
L[224] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[225] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[226] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[227] = 9'bxx_xx_xxxxx; // []
L[228] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[229] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[230] = 9'bxx_xx_xxxxx; // []
L[231] = 9'bxx_xx_xxxxx; // []
L[232] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[233] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[234] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[235] = 9'bxx_xx_xxxxx; // []
L[236] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[237] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[238] = 9'bxx_xx_xxxxx; // []
L[239] = 9'bxx_xx_xxxxx; // []
L[240] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[241] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[242] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[243] = 9'bxx_xx_xxxxx; // []
L[244] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[245] = 9'b00_01_00011; // [AX]->T
L[246] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[247] = 9'b10_01_00101; // T->[AX]
L[248] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[249] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[250] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[251] = 9'bxx_xx_xxxxx; // []
L[252] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[253] = 9'b00_01_00011; // [AX]->T
L[254] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[255] = 9'b10_01_00101; // T->[AX]
L[256] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[257] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[258] = 9'b00_10_10100; // ['PCH->[SP--]', 'PCL->[SP--],', 'PCH->[SP--](KEEPAC)', 'PCL->[SP--](KEEPAC)']
L[259] = 9'b00_10_10100; // ['PCH->[SP--]', 'PCL->[SP--],', 'PCH->[SP--](KEEPAC)', 'PCL->[SP--](KEEPAC)']
L[260] = 9'b00_10_00111; // KEEP_AC
L[261] = 9'b10_00_10011; // [PC]:T->PC
L[262] = 9'bxx_xx_xxxxx; // []
L[263] = 9'bxx_xx_xxxxx; // []
L[264] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[265] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[266] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[267] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[268] = 9'b00_01_01011; // [AX]->AH,T->AL
L[269] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[270] = 9'bxx_xx_xxxxx; // []
L[271] = 9'bxx_xx_xxxxx; // []
L[272] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[273] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[274] = 9'bxx_xx_xxxxx; // []
L[275] = 9'bxx_xx_xxxxx; // []
L[276] = 9'bxx_xx_xxxxx; // []
L[277] = 9'bxx_xx_xxxxx; // []
L[278] = 9'bxx_xx_xxxxx; // []
L[279] = 9'bxx_xx_xxxxx; // []
L[280] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[281] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[282] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[283] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[284] = 9'b00_01_01011; // [AX]->AH,T->AL
L[285] = 9'b00_01_00011; // [AX]->T
L[286] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[287] = 9'b10_01_00101; // T->[AX]
L[288] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[289] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[290] = 9'bxx_xx_xxxxx; // []
L[291] = 9'bxx_xx_xxxxx; // []
L[292] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[293] = 9'bxx_xx_xxxxx; // []
L[294] = 9'bxx_xx_xxxxx; // []
L[295] = 9'bxx_xx_xxxxx; // []
L[296] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[297] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[298] = 9'bxx_xx_xxxxx; // []
L[299] = 9'bxx_xx_xxxxx; // []
L[300] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[301] = 9'bxx_xx_xxxxx; // []
L[302] = 9'bxx_xx_xxxxx; // []
L[303] = 9'bxx_xx_xxxxx; // []
L[304] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[305] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[306] = 9'bxx_xx_xxxxx; // []
L[307] = 9'bxx_xx_xxxxx; // []
L[308] = 9'b00_01_00011; // [AX]->T
L[309] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[310] = 9'b10_01_00101; // T->[AX]
L[311] = 9'bxx_xx_xxxxx; // []
L[312] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[313] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[314] = 9'bxx_xx_xxxxx; // []
L[315] = 9'bxx_xx_xxxxx; // []
L[316] = 9'b00_01_00011; // [AX]->T
L[317] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[318] = 9'b10_01_00101; // T->[AX]
L[319] = 9'bxx_xx_xxxxx; // []
L[320] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[321] = 9'b00_00_00011; // [PC]->
L[322] = 9'b00_10_10000; // ['SP++', 'SP+1->SP', '[SP]->T,SP+1->SP']
L[323] = 9'b10_10_00010; // ['ALU([SP])->A', '[SP]->P']
L[324] = 9'bxx_xx_xxxxx; // []
L[325] = 9'bxx_xx_xxxxx; // []
L[326] = 9'bxx_xx_xxxxx; // []
L[327] = 9'bxx_xx_xxxxx; // []
L[328] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[329] = 9'b10_00_01101; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
L[330] = 9'bxx_xx_xxxxx; // []
L[331] = 9'bxx_xx_xxxxx; // []
L[332] = 9'bxx_xx_xxxxx; // []
L[333] = 9'bxx_xx_xxxxx; // []
L[334] = 9'bxx_xx_xxxxx; // []
L[335] = 9'bxx_xx_xxxxx; // []
L[336] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[337] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[338] = 9'bxx_xx_xxxxx; // []
L[339] = 9'bxx_xx_xxxxx; // []
L[340] = 9'bxx_xx_xxxxx; // []
L[341] = 9'bxx_xx_xxxxx; // []
L[342] = 9'bxx_xx_xxxxx; // []
L[343] = 9'bxx_xx_xxxxx; // []
L[344] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[345] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[346] = 9'bxx_xx_xxxxx; // []
L[347] = 9'bxx_xx_xxxxx; // []
L[348] = 9'bxx_xx_xxxxx; // []
L[349] = 9'bxx_xx_xxxxx; // []
L[350] = 9'bxx_xx_xxxxx; // []
L[351] = 9'bxx_xx_xxxxx; // []
L[352] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[353] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[354] = 9'b11_00_00001; // [PC++]->AH
L[355] = 9'bxx_xx_xxxxx; // []
L[356] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[357] = 9'bxx_xx_xxxxx; // []
L[358] = 9'bxx_xx_xxxxx; // []
L[359] = 9'bxx_xx_xxxxx; // []
L[360] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[361] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[362] = 9'b11_00_00001; // [PC++]->AH
L[363] = 9'bxx_xx_xxxxx; // []
L[364] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[365] = 9'bxx_xx_xxxxx; // []
L[366] = 9'bxx_xx_xxxxx; // []
L[367] = 9'bxx_xx_xxxxx; // []
L[368] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[369] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[370] = 9'b11_00_00001; // [PC++]->AH
L[371] = 9'bxx_xx_xxxxx; // []
L[372] = 9'b00_01_00011; // [AX]->T
L[373] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[374] = 9'b10_01_00101; // T->[AX]
L[375] = 9'bxx_xx_xxxxx; // []
L[376] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[377] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[378] = 9'b11_00_00001; // [PC++]->AH
L[379] = 9'bxx_xx_xxxxx; // []
L[380] = 9'b00_01_00011; // [AX]->T
L[381] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[382] = 9'b10_01_00101; // T->[AX]
L[383] = 9'bxx_xx_xxxxx; // []
L[384] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[385] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[386] = 9'b11_00_10001; // PC+T->PC
L[387] = 9'bxx_xx_xxxxx; // []
L[388] = 9'b10_00_00011; // ['NO-OP', '']
L[389] = 9'bxx_xx_xxxxx; // []
L[390] = 9'bxx_xx_xxxxx; // []
L[391] = 9'bxx_xx_xxxxx; // []
L[392] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[393] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[394] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[395] = 9'b01_01_01100; // [AX]->AH,T+Y->AL
L[396] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[397] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[398] = 9'bxx_xx_xxxxx; // []
L[399] = 9'bxx_xx_xxxxx; // []
L[400] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[401] = 9'b10_00_00011; // ['NO-OP', '']
L[402] = 9'bxx_xx_xxxxx; // []
L[403] = 9'bxx_xx_xxxxx; // []
L[404] = 9'bxx_xx_xxxxx; // []
L[405] = 9'bxx_xx_xxxxx; // []
L[406] = 9'bxx_xx_xxxxx; // []
L[407] = 9'bxx_xx_xxxxx; // []
L[408] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[409] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[410] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[411] = 9'b00_01_01100; // [AX]->AH,T+Y->AL
L[412] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[413] = 9'b00_01_00011; // [AX]->T
L[414] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[415] = 9'b10_01_00101; // T->[AX]
L[416] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[417] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[418] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[419] = 9'bxx_xx_xxxxx; // []
L[420] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[421] = 9'bxx_xx_xxxxx; // []
L[422] = 9'bxx_xx_xxxxx; // []
L[423] = 9'bxx_xx_xxxxx; // []
L[424] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[425] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[426] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[427] = 9'bxx_xx_xxxxx; // []
L[428] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[429] = 9'bxx_xx_xxxxx; // []
L[430] = 9'bxx_xx_xxxxx; // []
L[431] = 9'bxx_xx_xxxxx; // []
L[432] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[433] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[434] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[435] = 9'bxx_xx_xxxxx; // []
L[436] = 9'b00_01_00011; // [AX]->T
L[437] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[438] = 9'b10_01_00101; // T->[AX]
L[439] = 9'bxx_xx_xxxxx; // []
L[440] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[441] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[442] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[443] = 9'bxx_xx_xxxxx; // []
L[444] = 9'b00_01_00011; // [AX]->T
L[445] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[446] = 9'b10_01_00101; // T->[AX]
L[447] = 9'bxx_xx_xxxxx; // []
L[448] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[449] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[450] = 9'bxx_xx_xxxxx; // []
L[451] = 9'bxx_xx_xxxxx; // []
L[452] = 9'bxx_xx_xxxxx; // []
L[453] = 9'bxx_xx_xxxxx; // []
L[454] = 9'bxx_xx_xxxxx; // []
L[455] = 9'bxx_xx_xxxxx; // []
L[456] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[457] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[458] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[459] = 9'bxx_xx_xxxxx; // []
L[460] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[461] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[462] = 9'bxx_xx_xxxxx; // []
L[463] = 9'bxx_xx_xxxxx; // []
L[464] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[465] = 9'b10_00_00011; // ['NO-OP', '']
L[466] = 9'bxx_xx_xxxxx; // []
L[467] = 9'bxx_xx_xxxxx; // []
L[468] = 9'bxx_xx_xxxxx; // []
L[469] = 9'bxx_xx_xxxxx; // []
L[470] = 9'bxx_xx_xxxxx; // []
L[471] = 9'bxx_xx_xxxxx; // []
L[472] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[473] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[474] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[475] = 9'bxx_xx_xxxxx; // []
L[476] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[477] = 9'b00_01_00011; // [AX]->T
L[478] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[479] = 9'b10_01_00101; // T->[AX]
L[480] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[481] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[482] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[483] = 9'bxx_xx_xxxxx; // []
L[484] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[485] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[486] = 9'bxx_xx_xxxxx; // []
L[487] = 9'bxx_xx_xxxxx; // []
L[488] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[489] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[490] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[491] = 9'bxx_xx_xxxxx; // []
L[492] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[493] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[494] = 9'bxx_xx_xxxxx; // []
L[495] = 9'bxx_xx_xxxxx; // []
L[496] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[497] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[498] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[499] = 9'bxx_xx_xxxxx; // []
L[500] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[501] = 9'b00_01_00011; // [AX]->T
L[502] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[503] = 9'b10_01_00101; // T->[AX]
L[504] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[505] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[506] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[507] = 9'bxx_xx_xxxxx; // []
L[508] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[509] = 9'b00_01_00011; // [AX]->T
L[510] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[511] = 9'b10_01_00101; // T->[AX]
L[512] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[513] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[514] = 9'b00_10_10000; // ['SP++', 'SP+1->SP', '[SP]->T,SP+1->SP']
L[515] = 9'b00_10_10110; // [SP]->P,SP+1->SP
L[516] = 9'b00_10_10000; // ['SP++', 'SP+1->SP', '[SP]->T,SP+1->SP']
L[517] = 9'b10_10_10011; // [SP]:T->PC
L[518] = 9'bxx_xx_xxxxx; // []
L[519] = 9'bxx_xx_xxxxx; // []
L[520] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[521] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[522] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[523] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[524] = 9'b00_01_01011; // [AX]->AH,T->AL
L[525] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[526] = 9'bxx_xx_xxxxx; // []
L[527] = 9'bxx_xx_xxxxx; // []
L[528] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[529] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[530] = 9'bxx_xx_xxxxx; // []
L[531] = 9'bxx_xx_xxxxx; // []
L[532] = 9'bxx_xx_xxxxx; // []
L[533] = 9'bxx_xx_xxxxx; // []
L[534] = 9'bxx_xx_xxxxx; // []
L[535] = 9'bxx_xx_xxxxx; // []
L[536] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[537] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[538] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[539] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[540] = 9'b00_01_01011; // [AX]->AH,T->AL
L[541] = 9'b00_01_00011; // [AX]->T
L[542] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[543] = 9'b10_01_00101; // T->[AX]
L[544] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[545] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[546] = 9'bxx_xx_xxxxx; // []
L[547] = 9'bxx_xx_xxxxx; // []
L[548] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[549] = 9'bxx_xx_xxxxx; // []
L[550] = 9'bxx_xx_xxxxx; // []
L[551] = 9'bxx_xx_xxxxx; // []
L[552] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[553] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[554] = 9'bxx_xx_xxxxx; // []
L[555] = 9'bxx_xx_xxxxx; // []
L[556] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[557] = 9'bxx_xx_xxxxx; // []
L[558] = 9'bxx_xx_xxxxx; // []
L[559] = 9'bxx_xx_xxxxx; // []
L[560] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[561] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[562] = 9'bxx_xx_xxxxx; // []
L[563] = 9'bxx_xx_xxxxx; // []
L[564] = 9'b00_01_00011; // [AX]->T
L[565] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[566] = 9'b10_01_00101; // T->[AX]
L[567] = 9'bxx_xx_xxxxx; // []
L[568] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[569] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[570] = 9'bxx_xx_xxxxx; // []
L[571] = 9'bxx_xx_xxxxx; // []
L[572] = 9'b00_01_00011; // [AX]->T
L[573] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[574] = 9'b10_01_00101; // T->[AX]
L[575] = 9'bxx_xx_xxxxx; // []
L[576] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[577] = 9'b00_00_00011; // [PC]->
L[578] = 9'b10_10_01110; // ALU(A)->[SP--]
L[579] = 9'bxx_xx_xxxxx; // []
L[580] = 9'bxx_xx_xxxxx; // []
L[581] = 9'bxx_xx_xxxxx; // []
L[582] = 9'bxx_xx_xxxxx; // []
L[583] = 9'bxx_xx_xxxxx; // []
L[584] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[585] = 9'b10_00_01101; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
L[586] = 9'bxx_xx_xxxxx; // []
L[587] = 9'bxx_xx_xxxxx; // []
L[588] = 9'bxx_xx_xxxxx; // []
L[589] = 9'bxx_xx_xxxxx; // []
L[590] = 9'bxx_xx_xxxxx; // []
L[591] = 9'bxx_xx_xxxxx; // []
L[592] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[593] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[594] = 9'bxx_xx_xxxxx; // []
L[595] = 9'bxx_xx_xxxxx; // []
L[596] = 9'bxx_xx_xxxxx; // []
L[597] = 9'bxx_xx_xxxxx; // []
L[598] = 9'bxx_xx_xxxxx; // []
L[599] = 9'bxx_xx_xxxxx; // []
L[600] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[601] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[602] = 9'bxx_xx_xxxxx; // []
L[603] = 9'bxx_xx_xxxxx; // []
L[604] = 9'bxx_xx_xxxxx; // []
L[605] = 9'bxx_xx_xxxxx; // []
L[606] = 9'bxx_xx_xxxxx; // []
L[607] = 9'bxx_xx_xxxxx; // []
L[608] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[609] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[610] = 9'bxx_xx_xxxxx; // []
L[611] = 9'bxx_xx_xxxxx; // []
L[612] = 9'b10_00_10011; // [PC]:T->PC
L[613] = 9'bxx_xx_xxxxx; // []
L[614] = 9'bxx_xx_xxxxx; // []
L[615] = 9'bxx_xx_xxxxx; // []
L[616] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[617] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[618] = 9'b11_00_00001; // [PC++]->AH
L[619] = 9'bxx_xx_xxxxx; // []
L[620] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[621] = 9'bxx_xx_xxxxx; // []
L[622] = 9'bxx_xx_xxxxx; // []
L[623] = 9'bxx_xx_xxxxx; // []
L[624] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[625] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[626] = 9'b11_00_00001; // [PC++]->AH
L[627] = 9'bxx_xx_xxxxx; // []
L[628] = 9'b00_01_00011; // [AX]->T
L[629] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[630] = 9'b10_01_00101; // T->[AX]
L[631] = 9'bxx_xx_xxxxx; // []
L[632] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[633] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[634] = 9'b11_00_00001; // [PC++]->AH
L[635] = 9'bxx_xx_xxxxx; // []
L[636] = 9'b00_01_00011; // [AX]->T
L[637] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[638] = 9'b10_01_00101; // T->[AX]
L[639] = 9'bxx_xx_xxxxx; // []
L[640] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[641] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[642] = 9'b11_00_10001; // PC+T->PC
L[643] = 9'bxx_xx_xxxxx; // []
L[644] = 9'b10_00_00011; // ['NO-OP', '']
L[645] = 9'bxx_xx_xxxxx; // []
L[646] = 9'bxx_xx_xxxxx; // []
L[647] = 9'bxx_xx_xxxxx; // []
L[648] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[649] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[650] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[651] = 9'b01_01_01100; // [AX]->AH,T+Y->AL
L[652] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[653] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[654] = 9'bxx_xx_xxxxx; // []
L[655] = 9'bxx_xx_xxxxx; // []
L[656] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[657] = 9'b10_00_00011; // ['NO-OP', '']
L[658] = 9'bxx_xx_xxxxx; // []
L[659] = 9'bxx_xx_xxxxx; // []
L[660] = 9'bxx_xx_xxxxx; // []
L[661] = 9'bxx_xx_xxxxx; // []
L[662] = 9'bxx_xx_xxxxx; // []
L[663] = 9'bxx_xx_xxxxx; // []
L[664] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[665] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[666] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[667] = 9'b00_01_01100; // [AX]->AH,T+Y->AL
L[668] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[669] = 9'b00_01_00011; // [AX]->T
L[670] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[671] = 9'b10_01_00101; // T->[AX]
L[672] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[673] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[674] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[675] = 9'bxx_xx_xxxxx; // []
L[676] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[677] = 9'bxx_xx_xxxxx; // []
L[678] = 9'bxx_xx_xxxxx; // []
L[679] = 9'bxx_xx_xxxxx; // []
L[680] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[681] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[682] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[683] = 9'bxx_xx_xxxxx; // []
L[684] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[685] = 9'bxx_xx_xxxxx; // []
L[686] = 9'bxx_xx_xxxxx; // []
L[687] = 9'bxx_xx_xxxxx; // []
L[688] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[689] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[690] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[691] = 9'bxx_xx_xxxxx; // []
L[692] = 9'b00_01_00011; // [AX]->T
L[693] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[694] = 9'b10_01_00101; // T->[AX]
L[695] = 9'bxx_xx_xxxxx; // []
L[696] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[697] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[698] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[699] = 9'bxx_xx_xxxxx; // []
L[700] = 9'b00_01_00011; // [AX]->T
L[701] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[702] = 9'b10_01_00101; // T->[AX]
L[703] = 9'bxx_xx_xxxxx; // []
L[704] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[705] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[706] = 9'bxx_xx_xxxxx; // []
L[707] = 9'bxx_xx_xxxxx; // []
L[708] = 9'bxx_xx_xxxxx; // []
L[709] = 9'bxx_xx_xxxxx; // []
L[710] = 9'bxx_xx_xxxxx; // []
L[711] = 9'bxx_xx_xxxxx; // []
L[712] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[713] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[714] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[715] = 9'bxx_xx_xxxxx; // []
L[716] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[717] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[718] = 9'bxx_xx_xxxxx; // []
L[719] = 9'bxx_xx_xxxxx; // []
L[720] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[721] = 9'b10_00_00011; // ['NO-OP', '']
L[722] = 9'bxx_xx_xxxxx; // []
L[723] = 9'bxx_xx_xxxxx; // []
L[724] = 9'bxx_xx_xxxxx; // []
L[725] = 9'bxx_xx_xxxxx; // []
L[726] = 9'bxx_xx_xxxxx; // []
L[727] = 9'bxx_xx_xxxxx; // []
L[728] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[729] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[730] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[731] = 9'bxx_xx_xxxxx; // []
L[732] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[733] = 9'b00_01_00011; // [AX]->T
L[734] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[735] = 9'b10_01_00101; // T->[AX]
L[736] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[737] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[738] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[739] = 9'bxx_xx_xxxxx; // []
L[740] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[741] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[742] = 9'bxx_xx_xxxxx; // []
L[743] = 9'bxx_xx_xxxxx; // []
L[744] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[745] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[746] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[747] = 9'bxx_xx_xxxxx; // []
L[748] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[749] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[750] = 9'bxx_xx_xxxxx; // []
L[751] = 9'bxx_xx_xxxxx; // []
L[752] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[753] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[754] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[755] = 9'bxx_xx_xxxxx; // []
L[756] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[757] = 9'b00_01_00011; // [AX]->T
L[758] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[759] = 9'b10_01_00101; // T->[AX]
L[760] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[761] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[762] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[763] = 9'bxx_xx_xxxxx; // []
L[764] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[765] = 9'b00_01_00011; // [AX]->T
L[766] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[767] = 9'b10_01_00101; // T->[AX]
L[768] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[769] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[770] = 9'b11_10_10000; // SP+1->SP
L[771] = 9'bxx_xx_xxxxx; // []
L[772] = 9'b00_10_10000; // ['SP++', 'SP+1->SP', '[SP]->T,SP+1->SP']
L[773] = 9'b00_10_10011; // [SP]:T->PC
L[774] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[775] = 9'bxx_xx_xxxxx; // []
L[776] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[777] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[778] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[779] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[780] = 9'b00_01_01011; // [AX]->AH,T->AL
L[781] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[782] = 9'bxx_xx_xxxxx; // []
L[783] = 9'bxx_xx_xxxxx; // []
L[784] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[785] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[786] = 9'bxx_xx_xxxxx; // []
L[787] = 9'bxx_xx_xxxxx; // []
L[788] = 9'bxx_xx_xxxxx; // []
L[789] = 9'bxx_xx_xxxxx; // []
L[790] = 9'bxx_xx_xxxxx; // []
L[791] = 9'bxx_xx_xxxxx; // []
L[792] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[793] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[794] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[795] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[796] = 9'b00_01_01011; // [AX]->AH,T->AL
L[797] = 9'b00_01_00011; // [AX]->T
L[798] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[799] = 9'b10_01_00101; // T->[AX]
L[800] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[801] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[802] = 9'bxx_xx_xxxxx; // []
L[803] = 9'bxx_xx_xxxxx; // []
L[804] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[805] = 9'bxx_xx_xxxxx; // []
L[806] = 9'bxx_xx_xxxxx; // []
L[807] = 9'bxx_xx_xxxxx; // []
L[808] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[809] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[810] = 9'bxx_xx_xxxxx; // []
L[811] = 9'bxx_xx_xxxxx; // []
L[812] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[813] = 9'bxx_xx_xxxxx; // []
L[814] = 9'bxx_xx_xxxxx; // []
L[815] = 9'bxx_xx_xxxxx; // []
L[816] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[817] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[818] = 9'bxx_xx_xxxxx; // []
L[819] = 9'bxx_xx_xxxxx; // []
L[820] = 9'b00_01_00011; // [AX]->T
L[821] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[822] = 9'b10_01_00101; // T->[AX]
L[823] = 9'bxx_xx_xxxxx; // []
L[824] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[825] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[826] = 9'bxx_xx_xxxxx; // []
L[827] = 9'bxx_xx_xxxxx; // []
L[828] = 9'b00_01_00011; // [AX]->T
L[829] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[830] = 9'b10_01_00101; // T->[AX]
L[831] = 9'bxx_xx_xxxxx; // []
L[832] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[833] = 9'b00_00_00011; // [PC]->
L[834] = 9'b00_10_10000; // ['SP++', 'SP+1->SP', '[SP]->T,SP+1->SP']
L[835] = 9'b10_10_00010; // ['ALU([SP])->A', '[SP]->P']
L[836] = 9'bxx_xx_xxxxx; // []
L[837] = 9'bxx_xx_xxxxx; // []
L[838] = 9'bxx_xx_xxxxx; // []
L[839] = 9'bxx_xx_xxxxx; // []
L[840] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[841] = 9'b10_00_01101; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
L[842] = 9'bxx_xx_xxxxx; // []
L[843] = 9'bxx_xx_xxxxx; // []
L[844] = 9'bxx_xx_xxxxx; // []
L[845] = 9'bxx_xx_xxxxx; // []
L[846] = 9'bxx_xx_xxxxx; // []
L[847] = 9'bxx_xx_xxxxx; // []
L[848] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[849] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[850] = 9'bxx_xx_xxxxx; // []
L[851] = 9'bxx_xx_xxxxx; // []
L[852] = 9'bxx_xx_xxxxx; // []
L[853] = 9'bxx_xx_xxxxx; // []
L[854] = 9'bxx_xx_xxxxx; // []
L[855] = 9'bxx_xx_xxxxx; // []
L[856] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[857] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[858] = 9'bxx_xx_xxxxx; // []
L[859] = 9'bxx_xx_xxxxx; // []
L[860] = 9'bxx_xx_xxxxx; // []
L[861] = 9'bxx_xx_xxxxx; // []
L[862] = 9'bxx_xx_xxxxx; // []
L[863] = 9'bxx_xx_xxxxx; // []
L[864] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[865] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[866] = 9'b00_00_00001; // [PC++]->AH
L[867] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[868] = 9'b10_01_10011; // [AX]:T->PC
L[869] = 9'bxx_xx_xxxxx; // []
L[870] = 9'bxx_xx_xxxxx; // []
L[871] = 9'bxx_xx_xxxxx; // []
L[872] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[873] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[874] = 9'b11_00_00001; // [PC++]->AH
L[875] = 9'bxx_xx_xxxxx; // []
L[876] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[877] = 9'bxx_xx_xxxxx; // []
L[878] = 9'bxx_xx_xxxxx; // []
L[879] = 9'bxx_xx_xxxxx; // []
L[880] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[881] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[882] = 9'b11_00_00001; // [PC++]->AH
L[883] = 9'bxx_xx_xxxxx; // []
L[884] = 9'b00_01_00011; // [AX]->T
L[885] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[886] = 9'b10_01_00101; // T->[AX]
L[887] = 9'bxx_xx_xxxxx; // []
L[888] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[889] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[890] = 9'b11_00_00001; // [PC++]->AH
L[891] = 9'bxx_xx_xxxxx; // []
L[892] = 9'b00_01_00011; // [AX]->T
L[893] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[894] = 9'b10_01_00101; // T->[AX]
L[895] = 9'bxx_xx_xxxxx; // []
L[896] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[897] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[898] = 9'b11_00_10001; // PC+T->PC
L[899] = 9'bxx_xx_xxxxx; // []
L[900] = 9'b10_00_00011; // ['NO-OP', '']
L[901] = 9'bxx_xx_xxxxx; // []
L[902] = 9'bxx_xx_xxxxx; // []
L[903] = 9'bxx_xx_xxxxx; // []
L[904] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[905] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[906] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[907] = 9'b01_01_01100; // [AX]->AH,T+Y->AL
L[908] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[909] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[910] = 9'bxx_xx_xxxxx; // []
L[911] = 9'bxx_xx_xxxxx; // []
L[912] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[913] = 9'b10_00_00011; // ['NO-OP', '']
L[914] = 9'bxx_xx_xxxxx; // []
L[915] = 9'bxx_xx_xxxxx; // []
L[916] = 9'bxx_xx_xxxxx; // []
L[917] = 9'bxx_xx_xxxxx; // []
L[918] = 9'bxx_xx_xxxxx; // []
L[919] = 9'bxx_xx_xxxxx; // []
L[920] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[921] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[922] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[923] = 9'b00_01_01100; // [AX]->AH,T+Y->AL
L[924] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[925] = 9'b00_01_00011; // [AX]->T
L[926] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[927] = 9'b10_01_00101; // T->[AX]
L[928] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[929] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[930] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[931] = 9'bxx_xx_xxxxx; // []
L[932] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[933] = 9'bxx_xx_xxxxx; // []
L[934] = 9'bxx_xx_xxxxx; // []
L[935] = 9'bxx_xx_xxxxx; // []
L[936] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[937] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[938] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[939] = 9'bxx_xx_xxxxx; // []
L[940] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[941] = 9'bxx_xx_xxxxx; // []
L[942] = 9'bxx_xx_xxxxx; // []
L[943] = 9'bxx_xx_xxxxx; // []
L[944] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[945] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[946] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[947] = 9'bxx_xx_xxxxx; // []
L[948] = 9'b00_01_00011; // [AX]->T
L[949] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[950] = 9'b10_01_00101; // T->[AX]
L[951] = 9'bxx_xx_xxxxx; // []
L[952] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[953] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[954] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[955] = 9'bxx_xx_xxxxx; // []
L[956] = 9'b00_01_00011; // [AX]->T
L[957] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[958] = 9'b10_01_00101; // T->[AX]
L[959] = 9'bxx_xx_xxxxx; // []
L[960] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[961] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[962] = 9'bxx_xx_xxxxx; // []
L[963] = 9'bxx_xx_xxxxx; // []
L[964] = 9'bxx_xx_xxxxx; // []
L[965] = 9'bxx_xx_xxxxx; // []
L[966] = 9'bxx_xx_xxxxx; // []
L[967] = 9'bxx_xx_xxxxx; // []
L[968] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[969] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[970] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[971] = 9'bxx_xx_xxxxx; // []
L[972] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[973] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[974] = 9'bxx_xx_xxxxx; // []
L[975] = 9'bxx_xx_xxxxx; // []
L[976] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[977] = 9'b10_00_00011; // ['NO-OP', '']
L[978] = 9'bxx_xx_xxxxx; // []
L[979] = 9'bxx_xx_xxxxx; // []
L[980] = 9'bxx_xx_xxxxx; // []
L[981] = 9'bxx_xx_xxxxx; // []
L[982] = 9'bxx_xx_xxxxx; // []
L[983] = 9'bxx_xx_xxxxx; // []
L[984] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[985] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[986] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[987] = 9'bxx_xx_xxxxx; // []
L[988] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[989] = 9'b00_01_00011; // [AX]->T
L[990] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[991] = 9'b10_01_00101; // T->[AX]
L[992] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[993] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[994] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[995] = 9'bxx_xx_xxxxx; // []
L[996] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[997] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[998] = 9'bxx_xx_xxxxx; // []
L[999] = 9'bxx_xx_xxxxx; // []
L[1000] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1001] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1002] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1003] = 9'bxx_xx_xxxxx; // []
L[1004] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1005] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1006] = 9'bxx_xx_xxxxx; // []
L[1007] = 9'bxx_xx_xxxxx; // []
L[1008] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1009] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1010] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1011] = 9'bxx_xx_xxxxx; // []
L[1012] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1013] = 9'b00_01_00011; // [AX]->T
L[1014] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1015] = 9'b10_01_00101; // T->[AX]
L[1016] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1017] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1018] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1019] = 9'bxx_xx_xxxxx; // []
L[1020] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1021] = 9'b00_01_00011; // [AX]->T
L[1022] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1023] = 9'b10_01_00101; // T->[AX]
L[1024] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1025] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[1026] = 9'bxx_xx_xxxxx; // []
L[1027] = 9'bxx_xx_xxxxx; // []
L[1028] = 9'bxx_xx_xxxxx; // []
L[1029] = 9'bxx_xx_xxxxx; // []
L[1030] = 9'bxx_xx_xxxxx; // []
L[1031] = 9'bxx_xx_xxxxx; // []
L[1032] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1033] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1034] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[1035] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1036] = 9'b00_01_01011; // [AX]->AH,T->AL
L[1037] = 9'b10_01_00110; // ALU()->[AX]
L[1038] = 9'bxx_xx_xxxxx; // []
L[1039] = 9'bxx_xx_xxxxx; // []
L[1040] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1041] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[1042] = 9'bxx_xx_xxxxx; // []
L[1043] = 9'bxx_xx_xxxxx; // []
L[1044] = 9'bxx_xx_xxxxx; // []
L[1045] = 9'bxx_xx_xxxxx; // []
L[1046] = 9'bxx_xx_xxxxx; // []
L[1047] = 9'bxx_xx_xxxxx; // []
L[1048] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1049] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1050] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[1051] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1052] = 9'b00_01_01011; // [AX]->AH,T->AL
L[1053] = 9'b10_01_00110; // ALU()->[AX]
L[1054] = 9'bxx_xx_xxxxx; // []
L[1055] = 9'bxx_xx_xxxxx; // []
L[1056] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1057] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1058] = 9'bxx_xx_xxxxx; // []
L[1059] = 9'bxx_xx_xxxxx; // []
L[1060] = 9'b10_01_00110; // ALU()->[AX]
L[1061] = 9'bxx_xx_xxxxx; // []
L[1062] = 9'bxx_xx_xxxxx; // []
L[1063] = 9'bxx_xx_xxxxx; // []
L[1064] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1065] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1066] = 9'bxx_xx_xxxxx; // []
L[1067] = 9'bxx_xx_xxxxx; // []
L[1068] = 9'b10_01_00110; // ALU()->[AX]
L[1069] = 9'bxx_xx_xxxxx; // []
L[1070] = 9'bxx_xx_xxxxx; // []
L[1071] = 9'bxx_xx_xxxxx; // []
L[1072] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1073] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1074] = 9'bxx_xx_xxxxx; // []
L[1075] = 9'bxx_xx_xxxxx; // []
L[1076] = 9'b10_01_00110; // ALU()->[AX]
L[1077] = 9'bxx_xx_xxxxx; // []
L[1078] = 9'bxx_xx_xxxxx; // []
L[1079] = 9'bxx_xx_xxxxx; // []
L[1080] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1081] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1082] = 9'bxx_xx_xxxxx; // []
L[1083] = 9'bxx_xx_xxxxx; // []
L[1084] = 9'b10_01_00110; // ALU()->[AX]
L[1085] = 9'bxx_xx_xxxxx; // []
L[1086] = 9'bxx_xx_xxxxx; // []
L[1087] = 9'bxx_xx_xxxxx; // []
L[1088] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1089] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[1090] = 9'bxx_xx_xxxxx; // []
L[1091] = 9'bxx_xx_xxxxx; // []
L[1092] = 9'bxx_xx_xxxxx; // []
L[1093] = 9'bxx_xx_xxxxx; // []
L[1094] = 9'bxx_xx_xxxxx; // []
L[1095] = 9'bxx_xx_xxxxx; // []
L[1096] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1097] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[1098] = 9'bxx_xx_xxxxx; // []
L[1099] = 9'bxx_xx_xxxxx; // []
L[1100] = 9'bxx_xx_xxxxx; // []
L[1101] = 9'bxx_xx_xxxxx; // []
L[1102] = 9'bxx_xx_xxxxx; // []
L[1103] = 9'bxx_xx_xxxxx; // []
L[1104] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1105] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[1106] = 9'bxx_xx_xxxxx; // []
L[1107] = 9'bxx_xx_xxxxx; // []
L[1108] = 9'bxx_xx_xxxxx; // []
L[1109] = 9'bxx_xx_xxxxx; // []
L[1110] = 9'bxx_xx_xxxxx; // []
L[1111] = 9'bxx_xx_xxxxx; // []
L[1112] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1113] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[1114] = 9'bxx_xx_xxxxx; // []
L[1115] = 9'bxx_xx_xxxxx; // []
L[1116] = 9'bxx_xx_xxxxx; // []
L[1117] = 9'bxx_xx_xxxxx; // []
L[1118] = 9'bxx_xx_xxxxx; // []
L[1119] = 9'bxx_xx_xxxxx; // []
L[1120] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1121] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1122] = 9'b11_00_00001; // [PC++]->AH
L[1123] = 9'bxx_xx_xxxxx; // []
L[1124] = 9'b10_01_00110; // ALU()->[AX]
L[1125] = 9'bxx_xx_xxxxx; // []
L[1126] = 9'bxx_xx_xxxxx; // []
L[1127] = 9'bxx_xx_xxxxx; // []
L[1128] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1129] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1130] = 9'b11_00_00001; // [PC++]->AH
L[1131] = 9'bxx_xx_xxxxx; // []
L[1132] = 9'b10_01_00110; // ALU()->[AX]
L[1133] = 9'bxx_xx_xxxxx; // []
L[1134] = 9'bxx_xx_xxxxx; // []
L[1135] = 9'bxx_xx_xxxxx; // []
L[1136] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1137] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1138] = 9'b11_00_00001; // [PC++]->AH
L[1139] = 9'bxx_xx_xxxxx; // []
L[1140] = 9'b10_01_00110; // ALU()->[AX]
L[1141] = 9'bxx_xx_xxxxx; // []
L[1142] = 9'bxx_xx_xxxxx; // []
L[1143] = 9'bxx_xx_xxxxx; // []
L[1144] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1145] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1146] = 9'b11_00_00001; // [PC++]->AH
L[1147] = 9'bxx_xx_xxxxx; // []
L[1148] = 9'b10_01_00110; // ALU()->[AX]
L[1149] = 9'bxx_xx_xxxxx; // []
L[1150] = 9'bxx_xx_xxxxx; // []
L[1151] = 9'bxx_xx_xxxxx; // []
L[1152] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1153] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[1154] = 9'b11_00_10001; // PC+T->PC
L[1155] = 9'bxx_xx_xxxxx; // []
L[1156] = 9'b10_00_00011; // ['NO-OP', '']
L[1157] = 9'bxx_xx_xxxxx; // []
L[1158] = 9'bxx_xx_xxxxx; // []
L[1159] = 9'bxx_xx_xxxxx; // []
L[1160] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1161] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1162] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1163] = 9'b00_01_01100; // [AX]->AH,T+Y->AL
L[1164] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1165] = 9'b10_01_00110; // ALU()->[AX]
L[1166] = 9'bxx_xx_xxxxx; // []
L[1167] = 9'bxx_xx_xxxxx; // []
L[1168] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1169] = 9'b10_00_00011; // ['NO-OP', '']
L[1170] = 9'bxx_xx_xxxxx; // []
L[1171] = 9'bxx_xx_xxxxx; // []
L[1172] = 9'bxx_xx_xxxxx; // []
L[1173] = 9'bxx_xx_xxxxx; // []
L[1174] = 9'bxx_xx_xxxxx; // []
L[1175] = 9'bxx_xx_xxxxx; // []
L[1176] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1177] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1178] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1179] = 9'b00_01_01100; // [AX]->AH,T+Y->AL
L[1180] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1181] = 9'b10_01_00110; // ALU()->[AX]
L[1182] = 9'bxx_xx_xxxxx; // []
L[1183] = 9'bxx_xx_xxxxx; // []
L[1184] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1185] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1186] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1187] = 9'bxx_xx_xxxxx; // []
L[1188] = 9'b10_01_00110; // ALU()->[AX]
L[1189] = 9'bxx_xx_xxxxx; // []
L[1190] = 9'bxx_xx_xxxxx; // []
L[1191] = 9'bxx_xx_xxxxx; // []
L[1192] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1193] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1194] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1195] = 9'bxx_xx_xxxxx; // []
L[1196] = 9'b10_01_00110; // ALU()->[AX]
L[1197] = 9'bxx_xx_xxxxx; // []
L[1198] = 9'bxx_xx_xxxxx; // []
L[1199] = 9'bxx_xx_xxxxx; // []
L[1200] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1201] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1202] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1203] = 9'bxx_xx_xxxxx; // []
L[1204] = 9'b10_01_00110; // ALU()->[AX]
L[1205] = 9'bxx_xx_xxxxx; // []
L[1206] = 9'bxx_xx_xxxxx; // []
L[1207] = 9'bxx_xx_xxxxx; // []
L[1208] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1209] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1210] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1211] = 9'bxx_xx_xxxxx; // []
L[1212] = 9'b10_01_00110; // ALU()->[AX]
L[1213] = 9'bxx_xx_xxxxx; // []
L[1214] = 9'bxx_xx_xxxxx; // []
L[1215] = 9'bxx_xx_xxxxx; // []
L[1216] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1217] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[1218] = 9'bxx_xx_xxxxx; // []
L[1219] = 9'bxx_xx_xxxxx; // []
L[1220] = 9'bxx_xx_xxxxx; // []
L[1221] = 9'bxx_xx_xxxxx; // []
L[1222] = 9'bxx_xx_xxxxx; // []
L[1223] = 9'bxx_xx_xxxxx; // []
L[1224] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1225] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1226] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1227] = 9'bxx_xx_xxxxx; // []
L[1228] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1229] = 9'b10_01_00110; // ALU()->[AX]
L[1230] = 9'bxx_xx_xxxxx; // []
L[1231] = 9'bxx_xx_xxxxx; // []
L[1232] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1233] = 9'b10_00_10010; // X->S
L[1234] = 9'bxx_xx_xxxxx; // []
L[1235] = 9'bxx_xx_xxxxx; // []
L[1236] = 9'bxx_xx_xxxxx; // []
L[1237] = 9'bxx_xx_xxxxx; // []
L[1238] = 9'bxx_xx_xxxxx; // []
L[1239] = 9'bxx_xx_xxxxx; // []
L[1240] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1241] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1242] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1243] = 9'bxx_xx_xxxxx; // []
L[1244] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1245] = 9'b10_01_00110; // ALU()->[AX]
L[1246] = 9'bxx_xx_xxxxx; // []
L[1247] = 9'bxx_xx_xxxxx; // []
L[1248] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1249] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1250] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1251] = 9'bxx_xx_xxxxx; // []
L[1252] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1253] = 9'b10_01_00110; // ALU()->[AX]
L[1254] = 9'bxx_xx_xxxxx; // []
L[1255] = 9'bxx_xx_xxxxx; // []
L[1256] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1257] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1258] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1259] = 9'bxx_xx_xxxxx; // []
L[1260] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1261] = 9'b10_01_00110; // ALU()->[AX]
L[1262] = 9'bxx_xx_xxxxx; // []
L[1263] = 9'bxx_xx_xxxxx; // []
L[1264] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1265] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1266] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1267] = 9'bxx_xx_xxxxx; // []
L[1268] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1269] = 9'b10_01_00110; // ALU()->[AX]
L[1270] = 9'bxx_xx_xxxxx; // []
L[1271] = 9'bxx_xx_xxxxx; // []
L[1272] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1273] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1274] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1275] = 9'bxx_xx_xxxxx; // []
L[1276] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1277] = 9'b10_01_00110; // ALU()->[AX]
L[1278] = 9'bxx_xx_xxxxx; // []
L[1279] = 9'bxx_xx_xxxxx; // []
L[1280] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1281] = 9'b10_00_01101; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
L[1282] = 9'bxx_xx_xxxxx; // []
L[1283] = 9'bxx_xx_xxxxx; // []
L[1284] = 9'bxx_xx_xxxxx; // []
L[1285] = 9'bxx_xx_xxxxx; // []
L[1286] = 9'bxx_xx_xxxxx; // []
L[1287] = 9'bxx_xx_xxxxx; // []
L[1288] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1289] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1290] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[1291] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1292] = 9'b00_01_01011; // [AX]->AH,T->AL
L[1293] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1294] = 9'bxx_xx_xxxxx; // []
L[1295] = 9'bxx_xx_xxxxx; // []
L[1296] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1297] = 9'b10_00_01101; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
L[1298] = 9'bxx_xx_xxxxx; // []
L[1299] = 9'bxx_xx_xxxxx; // []
L[1300] = 9'bxx_xx_xxxxx; // []
L[1301] = 9'bxx_xx_xxxxx; // []
L[1302] = 9'bxx_xx_xxxxx; // []
L[1303] = 9'bxx_xx_xxxxx; // []
L[1304] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1305] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1306] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[1307] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1308] = 9'b00_01_01011; // [AX]->AH,T->AL
L[1309] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1310] = 9'bxx_xx_xxxxx; // []
L[1311] = 9'bxx_xx_xxxxx; // []
L[1312] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1313] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1314] = 9'bxx_xx_xxxxx; // []
L[1315] = 9'bxx_xx_xxxxx; // []
L[1316] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1317] = 9'bxx_xx_xxxxx; // []
L[1318] = 9'bxx_xx_xxxxx; // []
L[1319] = 9'bxx_xx_xxxxx; // []
L[1320] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1321] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1322] = 9'bxx_xx_xxxxx; // []
L[1323] = 9'bxx_xx_xxxxx; // []
L[1324] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1325] = 9'bxx_xx_xxxxx; // []
L[1326] = 9'bxx_xx_xxxxx; // []
L[1327] = 9'bxx_xx_xxxxx; // []
L[1328] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1329] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1330] = 9'bxx_xx_xxxxx; // []
L[1331] = 9'bxx_xx_xxxxx; // []
L[1332] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1333] = 9'bxx_xx_xxxxx; // []
L[1334] = 9'bxx_xx_xxxxx; // []
L[1335] = 9'bxx_xx_xxxxx; // []
L[1336] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1337] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1338] = 9'bxx_xx_xxxxx; // []
L[1339] = 9'bxx_xx_xxxxx; // []
L[1340] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1341] = 9'bxx_xx_xxxxx; // []
L[1342] = 9'bxx_xx_xxxxx; // []
L[1343] = 9'bxx_xx_xxxxx; // []
L[1344] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1345] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[1346] = 9'bxx_xx_xxxxx; // []
L[1347] = 9'bxx_xx_xxxxx; // []
L[1348] = 9'bxx_xx_xxxxx; // []
L[1349] = 9'bxx_xx_xxxxx; // []
L[1350] = 9'bxx_xx_xxxxx; // []
L[1351] = 9'bxx_xx_xxxxx; // []
L[1352] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1353] = 9'b10_00_01101; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
L[1354] = 9'bxx_xx_xxxxx; // []
L[1355] = 9'bxx_xx_xxxxx; // []
L[1356] = 9'bxx_xx_xxxxx; // []
L[1357] = 9'bxx_xx_xxxxx; // []
L[1358] = 9'bxx_xx_xxxxx; // []
L[1359] = 9'bxx_xx_xxxxx; // []
L[1360] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1361] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[1362] = 9'bxx_xx_xxxxx; // []
L[1363] = 9'bxx_xx_xxxxx; // []
L[1364] = 9'bxx_xx_xxxxx; // []
L[1365] = 9'bxx_xx_xxxxx; // []
L[1366] = 9'bxx_xx_xxxxx; // []
L[1367] = 9'bxx_xx_xxxxx; // []
L[1368] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1369] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[1370] = 9'bxx_xx_xxxxx; // []
L[1371] = 9'bxx_xx_xxxxx; // []
L[1372] = 9'bxx_xx_xxxxx; // []
L[1373] = 9'bxx_xx_xxxxx; // []
L[1374] = 9'bxx_xx_xxxxx; // []
L[1375] = 9'bxx_xx_xxxxx; // []
L[1376] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1377] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1378] = 9'b11_00_00001; // [PC++]->AH
L[1379] = 9'bxx_xx_xxxxx; // []
L[1380] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1381] = 9'bxx_xx_xxxxx; // []
L[1382] = 9'bxx_xx_xxxxx; // []
L[1383] = 9'bxx_xx_xxxxx; // []
L[1384] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1385] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1386] = 9'b11_00_00001; // [PC++]->AH
L[1387] = 9'bxx_xx_xxxxx; // []
L[1388] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1389] = 9'bxx_xx_xxxxx; // []
L[1390] = 9'bxx_xx_xxxxx; // []
L[1391] = 9'bxx_xx_xxxxx; // []
L[1392] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1393] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1394] = 9'b11_00_00001; // [PC++]->AH
L[1395] = 9'bxx_xx_xxxxx; // []
L[1396] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1397] = 9'bxx_xx_xxxxx; // []
L[1398] = 9'bxx_xx_xxxxx; // []
L[1399] = 9'bxx_xx_xxxxx; // []
L[1400] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1401] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1402] = 9'b11_00_00001; // [PC++]->AH
L[1403] = 9'bxx_xx_xxxxx; // []
L[1404] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1405] = 9'bxx_xx_xxxxx; // []
L[1406] = 9'bxx_xx_xxxxx; // []
L[1407] = 9'bxx_xx_xxxxx; // []
L[1408] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1409] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[1410] = 9'b11_00_10001; // PC+T->PC
L[1411] = 9'bxx_xx_xxxxx; // []
L[1412] = 9'b10_00_00011; // ['NO-OP', '']
L[1413] = 9'bxx_xx_xxxxx; // []
L[1414] = 9'bxx_xx_xxxxx; // []
L[1415] = 9'bxx_xx_xxxxx; // []
L[1416] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1417] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1418] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1419] = 9'b01_01_01100; // [AX]->AH,T+Y->AL
L[1420] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1421] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1422] = 9'bxx_xx_xxxxx; // []
L[1423] = 9'bxx_xx_xxxxx; // []
L[1424] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1425] = 9'b10_00_00011; // ['NO-OP', '']
L[1426] = 9'bxx_xx_xxxxx; // []
L[1427] = 9'bxx_xx_xxxxx; // []
L[1428] = 9'bxx_xx_xxxxx; // []
L[1429] = 9'bxx_xx_xxxxx; // []
L[1430] = 9'bxx_xx_xxxxx; // []
L[1431] = 9'bxx_xx_xxxxx; // []
L[1432] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1433] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1434] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1435] = 9'b01_01_01100; // [AX]->AH,T+Y->AL
L[1436] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1437] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1438] = 9'bxx_xx_xxxxx; // []
L[1439] = 9'bxx_xx_xxxxx; // []
L[1440] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1441] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1442] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1443] = 9'bxx_xx_xxxxx; // []
L[1444] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1445] = 9'bxx_xx_xxxxx; // []
L[1446] = 9'bxx_xx_xxxxx; // []
L[1447] = 9'bxx_xx_xxxxx; // []
L[1448] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1449] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1450] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1451] = 9'bxx_xx_xxxxx; // []
L[1452] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1453] = 9'bxx_xx_xxxxx; // []
L[1454] = 9'bxx_xx_xxxxx; // []
L[1455] = 9'bxx_xx_xxxxx; // []
L[1456] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1457] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1458] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1459] = 9'bxx_xx_xxxxx; // []
L[1460] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1461] = 9'bxx_xx_xxxxx; // []
L[1462] = 9'bxx_xx_xxxxx; // []
L[1463] = 9'bxx_xx_xxxxx; // []
L[1464] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1465] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1466] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1467] = 9'bxx_xx_xxxxx; // []
L[1468] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1469] = 9'bxx_xx_xxxxx; // []
L[1470] = 9'bxx_xx_xxxxx; // []
L[1471] = 9'bxx_xx_xxxxx; // []
L[1472] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1473] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[1474] = 9'bxx_xx_xxxxx; // []
L[1475] = 9'bxx_xx_xxxxx; // []
L[1476] = 9'bxx_xx_xxxxx; // []
L[1477] = 9'bxx_xx_xxxxx; // []
L[1478] = 9'bxx_xx_xxxxx; // []
L[1479] = 9'bxx_xx_xxxxx; // []
L[1480] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1481] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1482] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1483] = 9'bxx_xx_xxxxx; // []
L[1484] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1485] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1486] = 9'bxx_xx_xxxxx; // []
L[1487] = 9'bxx_xx_xxxxx; // []
L[1488] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1489] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[1490] = 9'bxx_xx_xxxxx; // []
L[1491] = 9'bxx_xx_xxxxx; // []
L[1492] = 9'bxx_xx_xxxxx; // []
L[1493] = 9'bxx_xx_xxxxx; // []
L[1494] = 9'bxx_xx_xxxxx; // []
L[1495] = 9'bxx_xx_xxxxx; // []
L[1496] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1497] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1498] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1499] = 9'bxx_xx_xxxxx; // []
L[1500] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1501] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1502] = 9'bxx_xx_xxxxx; // []
L[1503] = 9'bxx_xx_xxxxx; // []
L[1504] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1505] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1506] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1507] = 9'bxx_xx_xxxxx; // []
L[1508] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1509] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1510] = 9'bxx_xx_xxxxx; // []
L[1511] = 9'bxx_xx_xxxxx; // []
L[1512] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1513] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1514] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1515] = 9'bxx_xx_xxxxx; // []
L[1516] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1517] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1518] = 9'bxx_xx_xxxxx; // []
L[1519] = 9'bxx_xx_xxxxx; // []
L[1520] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1521] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1522] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1523] = 9'bxx_xx_xxxxx; // []
L[1524] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1525] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1526] = 9'bxx_xx_xxxxx; // []
L[1527] = 9'bxx_xx_xxxxx; // []
L[1528] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1529] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1530] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1531] = 9'bxx_xx_xxxxx; // []
L[1532] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1533] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1534] = 9'bxx_xx_xxxxx; // []
L[1535] = 9'bxx_xx_xxxxx; // []
L[1536] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1537] = 9'b10_00_01101; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
L[1538] = 9'bxx_xx_xxxxx; // []
L[1539] = 9'bxx_xx_xxxxx; // []
L[1540] = 9'bxx_xx_xxxxx; // []
L[1541] = 9'bxx_xx_xxxxx; // []
L[1542] = 9'bxx_xx_xxxxx; // []
L[1543] = 9'bxx_xx_xxxxx; // []
L[1544] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1545] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1546] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[1547] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1548] = 9'b00_01_01011; // [AX]->AH,T->AL
L[1549] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1550] = 9'bxx_xx_xxxxx; // []
L[1551] = 9'bxx_xx_xxxxx; // []
L[1552] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1553] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[1554] = 9'bxx_xx_xxxxx; // []
L[1555] = 9'bxx_xx_xxxxx; // []
L[1556] = 9'bxx_xx_xxxxx; // []
L[1557] = 9'bxx_xx_xxxxx; // []
L[1558] = 9'bxx_xx_xxxxx; // []
L[1559] = 9'bxx_xx_xxxxx; // []
L[1560] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1561] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1562] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[1563] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1564] = 9'b00_01_01011; // [AX]->AH,T->AL
L[1565] = 9'b00_01_00011; // [AX]->T
L[1566] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1567] = 9'b10_01_00101; // T->[AX]
L[1568] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1569] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1570] = 9'bxx_xx_xxxxx; // []
L[1571] = 9'bxx_xx_xxxxx; // []
L[1572] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1573] = 9'bxx_xx_xxxxx; // []
L[1574] = 9'bxx_xx_xxxxx; // []
L[1575] = 9'bxx_xx_xxxxx; // []
L[1576] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1577] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1578] = 9'bxx_xx_xxxxx; // []
L[1579] = 9'bxx_xx_xxxxx; // []
L[1580] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1581] = 9'bxx_xx_xxxxx; // []
L[1582] = 9'bxx_xx_xxxxx; // []
L[1583] = 9'bxx_xx_xxxxx; // []
L[1584] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1585] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1586] = 9'bxx_xx_xxxxx; // []
L[1587] = 9'bxx_xx_xxxxx; // []
L[1588] = 9'b00_01_00011; // [AX]->T
L[1589] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1590] = 9'b10_01_00101; // T->[AX]
L[1591] = 9'bxx_xx_xxxxx; // []
L[1592] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1593] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1594] = 9'bxx_xx_xxxxx; // []
L[1595] = 9'bxx_xx_xxxxx; // []
L[1596] = 9'b00_01_00011; // [AX]->T
L[1597] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1598] = 9'b10_01_00101; // T->[AX]
L[1599] = 9'bxx_xx_xxxxx; // []
L[1600] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1601] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[1602] = 9'bxx_xx_xxxxx; // []
L[1603] = 9'bxx_xx_xxxxx; // []
L[1604] = 9'bxx_xx_xxxxx; // []
L[1605] = 9'bxx_xx_xxxxx; // []
L[1606] = 9'bxx_xx_xxxxx; // []
L[1607] = 9'bxx_xx_xxxxx; // []
L[1608] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1609] = 9'b10_00_01101; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
L[1610] = 9'bxx_xx_xxxxx; // []
L[1611] = 9'bxx_xx_xxxxx; // []
L[1612] = 9'bxx_xx_xxxxx; // []
L[1613] = 9'bxx_xx_xxxxx; // []
L[1614] = 9'bxx_xx_xxxxx; // []
L[1615] = 9'bxx_xx_xxxxx; // []
L[1616] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1617] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[1618] = 9'bxx_xx_xxxxx; // []
L[1619] = 9'bxx_xx_xxxxx; // []
L[1620] = 9'bxx_xx_xxxxx; // []
L[1621] = 9'bxx_xx_xxxxx; // []
L[1622] = 9'bxx_xx_xxxxx; // []
L[1623] = 9'bxx_xx_xxxxx; // []
L[1624] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1625] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[1626] = 9'bxx_xx_xxxxx; // []
L[1627] = 9'bxx_xx_xxxxx; // []
L[1628] = 9'bxx_xx_xxxxx; // []
L[1629] = 9'bxx_xx_xxxxx; // []
L[1630] = 9'bxx_xx_xxxxx; // []
L[1631] = 9'bxx_xx_xxxxx; // []
L[1632] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1633] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1634] = 9'b11_00_00001; // [PC++]->AH
L[1635] = 9'bxx_xx_xxxxx; // []
L[1636] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1637] = 9'bxx_xx_xxxxx; // []
L[1638] = 9'bxx_xx_xxxxx; // []
L[1639] = 9'bxx_xx_xxxxx; // []
L[1640] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1641] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1642] = 9'b11_00_00001; // [PC++]->AH
L[1643] = 9'bxx_xx_xxxxx; // []
L[1644] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1645] = 9'bxx_xx_xxxxx; // []
L[1646] = 9'bxx_xx_xxxxx; // []
L[1647] = 9'bxx_xx_xxxxx; // []
L[1648] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1649] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1650] = 9'b11_00_00001; // [PC++]->AH
L[1651] = 9'bxx_xx_xxxxx; // []
L[1652] = 9'b00_01_00011; // [AX]->T
L[1653] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1654] = 9'b10_01_00101; // T->[AX]
L[1655] = 9'bxx_xx_xxxxx; // []
L[1656] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1657] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1658] = 9'b11_00_00001; // [PC++]->AH
L[1659] = 9'bxx_xx_xxxxx; // []
L[1660] = 9'b00_01_00011; // [AX]->T
L[1661] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1662] = 9'b10_01_00101; // T->[AX]
L[1663] = 9'bxx_xx_xxxxx; // []
L[1664] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1665] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[1666] = 9'b11_00_10001; // PC+T->PC
L[1667] = 9'bxx_xx_xxxxx; // []
L[1668] = 9'b10_00_00011; // ['NO-OP', '']
L[1669] = 9'bxx_xx_xxxxx; // []
L[1670] = 9'bxx_xx_xxxxx; // []
L[1671] = 9'bxx_xx_xxxxx; // []
L[1672] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1673] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1674] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1675] = 9'b01_01_01100; // [AX]->AH,T+Y->AL
L[1676] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1677] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1678] = 9'bxx_xx_xxxxx; // []
L[1679] = 9'bxx_xx_xxxxx; // []
L[1680] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1681] = 9'b10_00_00011; // ['NO-OP', '']
L[1682] = 9'bxx_xx_xxxxx; // []
L[1683] = 9'bxx_xx_xxxxx; // []
L[1684] = 9'bxx_xx_xxxxx; // []
L[1685] = 9'bxx_xx_xxxxx; // []
L[1686] = 9'bxx_xx_xxxxx; // []
L[1687] = 9'bxx_xx_xxxxx; // []
L[1688] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1689] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1690] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1691] = 9'b00_01_01100; // [AX]->AH,T+Y->AL
L[1692] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1693] = 9'b00_01_00011; // [AX]->T
L[1694] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1695] = 9'b10_01_00101; // T->[AX]
L[1696] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1697] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1698] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1699] = 9'bxx_xx_xxxxx; // []
L[1700] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[1701] = 9'bxx_xx_xxxxx; // []
L[1702] = 9'bxx_xx_xxxxx; // []
L[1703] = 9'bxx_xx_xxxxx; // []
L[1704] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1705] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1706] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1707] = 9'bxx_xx_xxxxx; // []
L[1708] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1709] = 9'bxx_xx_xxxxx; // []
L[1710] = 9'bxx_xx_xxxxx; // []
L[1711] = 9'bxx_xx_xxxxx; // []
L[1712] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1713] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1714] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1715] = 9'bxx_xx_xxxxx; // []
L[1716] = 9'b00_01_00011; // [AX]->T
L[1717] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1718] = 9'b10_01_00101; // T->[AX]
L[1719] = 9'bxx_xx_xxxxx; // []
L[1720] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1721] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1722] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1723] = 9'bxx_xx_xxxxx; // []
L[1724] = 9'b00_01_00011; // [AX]->T
L[1725] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1726] = 9'b10_01_00101; // T->[AX]
L[1727] = 9'bxx_xx_xxxxx; // []
L[1728] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1729] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[1730] = 9'bxx_xx_xxxxx; // []
L[1731] = 9'bxx_xx_xxxxx; // []
L[1732] = 9'bxx_xx_xxxxx; // []
L[1733] = 9'bxx_xx_xxxxx; // []
L[1734] = 9'bxx_xx_xxxxx; // []
L[1735] = 9'bxx_xx_xxxxx; // []
L[1736] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1737] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1738] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1739] = 9'bxx_xx_xxxxx; // []
L[1740] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1741] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1742] = 9'bxx_xx_xxxxx; // []
L[1743] = 9'bxx_xx_xxxxx; // []
L[1744] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1745] = 9'b10_00_00011; // ['NO-OP', '']
L[1746] = 9'bxx_xx_xxxxx; // []
L[1747] = 9'bxx_xx_xxxxx; // []
L[1748] = 9'bxx_xx_xxxxx; // []
L[1749] = 9'bxx_xx_xxxxx; // []
L[1750] = 9'bxx_xx_xxxxx; // []
L[1751] = 9'bxx_xx_xxxxx; // []
L[1752] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1753] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1754] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1755] = 9'bxx_xx_xxxxx; // []
L[1756] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1757] = 9'b00_01_00011; // [AX]->T
L[1758] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1759] = 9'b10_01_00101; // T->[AX]
L[1760] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1761] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1762] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1763] = 9'bxx_xx_xxxxx; // []
L[1764] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1765] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[1766] = 9'bxx_xx_xxxxx; // []
L[1767] = 9'bxx_xx_xxxxx; // []
L[1768] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1769] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1770] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1771] = 9'bxx_xx_xxxxx; // []
L[1772] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1773] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1774] = 9'bxx_xx_xxxxx; // []
L[1775] = 9'bxx_xx_xxxxx; // []
L[1776] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1777] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1778] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1779] = 9'bxx_xx_xxxxx; // []
L[1780] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1781] = 9'b00_01_00011; // [AX]->T
L[1782] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1783] = 9'b10_01_00101; // T->[AX]
L[1784] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1785] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1786] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1787] = 9'bxx_xx_xxxxx; // []
L[1788] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1789] = 9'b00_01_00011; // [AX]->T
L[1790] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1791] = 9'b10_01_00101; // T->[AX]
L[1792] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1793] = 9'b10_00_01101; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
L[1794] = 9'bxx_xx_xxxxx; // []
L[1795] = 9'bxx_xx_xxxxx; // []
L[1796] = 9'bxx_xx_xxxxx; // []
L[1797] = 9'bxx_xx_xxxxx; // []
L[1798] = 9'bxx_xx_xxxxx; // []
L[1799] = 9'bxx_xx_xxxxx; // []
L[1800] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1801] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1802] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[1803] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1804] = 9'b00_01_01011; // [AX]->AH,T->AL
L[1805] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1806] = 9'bxx_xx_xxxxx; // []
L[1807] = 9'bxx_xx_xxxxx; // []
L[1808] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1809] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[1810] = 9'bxx_xx_xxxxx; // []
L[1811] = 9'bxx_xx_xxxxx; // []
L[1812] = 9'bxx_xx_xxxxx; // []
L[1813] = 9'bxx_xx_xxxxx; // []
L[1814] = 9'bxx_xx_xxxxx; // []
L[1815] = 9'bxx_xx_xxxxx; // []
L[1816] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1817] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1818] = 9'b00_01_00111; // [AX]->?,AL+X->AL
L[1819] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1820] = 9'b00_01_01011; // [AX]->AH,T->AL
L[1821] = 9'b00_01_00011; // [AX]->T
L[1822] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1823] = 9'b10_01_00101; // T->[AX]
L[1824] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1825] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1826] = 9'bxx_xx_xxxxx; // []
L[1827] = 9'bxx_xx_xxxxx; // []
L[1828] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1829] = 9'bxx_xx_xxxxx; // []
L[1830] = 9'bxx_xx_xxxxx; // []
L[1831] = 9'bxx_xx_xxxxx; // []
L[1832] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1833] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1834] = 9'bxx_xx_xxxxx; // []
L[1835] = 9'bxx_xx_xxxxx; // []
L[1836] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1837] = 9'bxx_xx_xxxxx; // []
L[1838] = 9'bxx_xx_xxxxx; // []
L[1839] = 9'bxx_xx_xxxxx; // []
L[1840] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1841] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1842] = 9'bxx_xx_xxxxx; // []
L[1843] = 9'bxx_xx_xxxxx; // []
L[1844] = 9'b00_01_00011; // [AX]->T
L[1845] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1846] = 9'b10_01_00101; // T->[AX]
L[1847] = 9'bxx_xx_xxxxx; // []
L[1848] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1849] = 9'b11_00_00000; // ['[PC++]->AL', '[PC++]->T']
L[1850] = 9'bxx_xx_xxxxx; // []
L[1851] = 9'bxx_xx_xxxxx; // []
L[1852] = 9'b00_01_00011; // [AX]->T
L[1853] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1854] = 9'b10_01_00101; // T->[AX]
L[1855] = 9'bxx_xx_xxxxx; // []
L[1856] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1857] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[1858] = 9'bxx_xx_xxxxx; // []
L[1859] = 9'bxx_xx_xxxxx; // []
L[1860] = 9'bxx_xx_xxxxx; // []
L[1861] = 9'bxx_xx_xxxxx; // []
L[1862] = 9'bxx_xx_xxxxx; // []
L[1863] = 9'bxx_xx_xxxxx; // []
L[1864] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1865] = 9'b10_00_01101; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
L[1866] = 9'bxx_xx_xxxxx; // []
L[1867] = 9'bxx_xx_xxxxx; // []
L[1868] = 9'bxx_xx_xxxxx; // []
L[1869] = 9'bxx_xx_xxxxx; // []
L[1870] = 9'bxx_xx_xxxxx; // []
L[1871] = 9'bxx_xx_xxxxx; // []
L[1872] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1873] = 9'b10_00_00011; // ['NO-OP', '']
L[1874] = 9'bxx_xx_xxxxx; // []
L[1875] = 9'bxx_xx_xxxxx; // []
L[1876] = 9'bxx_xx_xxxxx; // []
L[1877] = 9'bxx_xx_xxxxx; // []
L[1878] = 9'bxx_xx_xxxxx; // []
L[1879] = 9'bxx_xx_xxxxx; // []
L[1880] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1881] = 9'b10_00_01101; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
L[1882] = 9'bxx_xx_xxxxx; // []
L[1883] = 9'bxx_xx_xxxxx; // []
L[1884] = 9'bxx_xx_xxxxx; // []
L[1885] = 9'bxx_xx_xxxxx; // []
L[1886] = 9'bxx_xx_xxxxx; // []
L[1887] = 9'bxx_xx_xxxxx; // []
L[1888] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1889] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1890] = 9'b11_00_00001; // [PC++]->AH
L[1891] = 9'bxx_xx_xxxxx; // []
L[1892] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1893] = 9'bxx_xx_xxxxx; // []
L[1894] = 9'bxx_xx_xxxxx; // []
L[1895] = 9'bxx_xx_xxxxx; // []
L[1896] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1897] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1898] = 9'b11_00_00001; // [PC++]->AH
L[1899] = 9'bxx_xx_xxxxx; // []
L[1900] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1901] = 9'bxx_xx_xxxxx; // []
L[1902] = 9'bxx_xx_xxxxx; // []
L[1903] = 9'bxx_xx_xxxxx; // []
L[1904] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1905] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1906] = 9'b11_00_00001; // [PC++]->AH
L[1907] = 9'bxx_xx_xxxxx; // []
L[1908] = 9'b00_01_00011; // [AX]->T
L[1909] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1910] = 9'b10_01_00101; // T->[AX]
L[1911] = 9'bxx_xx_xxxxx; // []
L[1912] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1913] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1914] = 9'b11_00_00001; // [PC++]->AH
L[1915] = 9'bxx_xx_xxxxx; // []
L[1916] = 9'b00_01_00011; // [AX]->T
L[1917] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1918] = 9'b10_01_00101; // T->[AX]
L[1919] = 9'bxx_xx_xxxxx; // []
L[1920] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1921] = 9'b10_00_00000; // ['[PC++]->?', 'PC+1->PC', '']
L[1922] = 9'b11_00_10001; // PC+T->PC
L[1923] = 9'bxx_xx_xxxxx; // []
L[1924] = 9'b10_00_00011; // ['NO-OP', '']
L[1925] = 9'bxx_xx_xxxxx; // []
L[1926] = 9'bxx_xx_xxxxx; // []
L[1927] = 9'bxx_xx_xxxxx; // []
L[1928] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1929] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1930] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1931] = 9'b01_01_01100; // [AX]->AH,T+Y->AL
L[1932] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1933] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1934] = 9'bxx_xx_xxxxx; // []
L[1935] = 9'bxx_xx_xxxxx; // []
L[1936] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1937] = 9'b10_00_00011; // ['NO-OP', '']
L[1938] = 9'bxx_xx_xxxxx; // []
L[1939] = 9'bxx_xx_xxxxx; // []
L[1940] = 9'bxx_xx_xxxxx; // []
L[1941] = 9'bxx_xx_xxxxx; // []
L[1942] = 9'bxx_xx_xxxxx; // []
L[1943] = 9'bxx_xx_xxxxx; // []
L[1944] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1945] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1946] = 9'b00_01_01010; // [AX]->T,AL+1->AL
L[1947] = 9'b00_01_01100; // [AX]->AH,T+Y->AL
L[1948] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1949] = 9'b00_01_00011; // [AX]->T
L[1950] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1951] = 9'b10_01_00101; // T->[AX]
L[1952] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1953] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1954] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1955] = 9'bxx_xx_xxxxx; // []
L[1956] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[1957] = 9'bxx_xx_xxxxx; // []
L[1958] = 9'bxx_xx_xxxxx; // []
L[1959] = 9'bxx_xx_xxxxx; // []
L[1960] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1961] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1962] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1963] = 9'bxx_xx_xxxxx; // []
L[1964] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1965] = 9'bxx_xx_xxxxx; // []
L[1966] = 9'bxx_xx_xxxxx; // []
L[1967] = 9'bxx_xx_xxxxx; // []
L[1968] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1969] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1970] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1971] = 9'bxx_xx_xxxxx; // []
L[1972] = 9'b00_01_00011; // [AX]->T
L[1973] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1974] = 9'b10_01_00101; // T->[AX]
L[1975] = 9'bxx_xx_xxxxx; // []
L[1976] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1977] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1978] = 9'b11_01_00111; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL']
L[1979] = 9'bxx_xx_xxxxx; // []
L[1980] = 9'b00_01_00011; // [AX]->T
L[1981] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[1982] = 9'b10_01_00101; // T->[AX]
L[1983] = 9'bxx_xx_xxxxx; // []
L[1984] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1985] = 9'b10_00_00010; // ['[PC]->,ALU()->A', 'Setappropriateflags', 'ALU()->X,Y', 'ALU()->A']
L[1986] = 9'bxx_xx_xxxxx; // []
L[1987] = 9'bxx_xx_xxxxx; // []
L[1988] = 9'bxx_xx_xxxxx; // []
L[1989] = 9'bxx_xx_xxxxx; // []
L[1990] = 9'bxx_xx_xxxxx; // []
L[1991] = 9'bxx_xx_xxxxx; // []
L[1992] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1993] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[1994] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[1995] = 9'bxx_xx_xxxxx; // []
L[1996] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[1997] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[1998] = 9'bxx_xx_xxxxx; // []
L[1999] = 9'bxx_xx_xxxxx; // []
L[2000] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[2001] = 9'b10_00_00011; // ['NO-OP', '']
L[2002] = 9'bxx_xx_xxxxx; // []
L[2003] = 9'bxx_xx_xxxxx; // []
L[2004] = 9'bxx_xx_xxxxx; // []
L[2005] = 9'bxx_xx_xxxxx; // []
L[2006] = 9'bxx_xx_xxxxx; // []
L[2007] = 9'bxx_xx_xxxxx; // []
L[2008] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[2009] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[2010] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[2011] = 9'bxx_xx_xxxxx; // []
L[2012] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[2013] = 9'b00_01_00011; // [AX]->T
L[2014] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[2015] = 9'b10_01_00101; // T->[AX]
L[2016] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[2017] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[2018] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[2019] = 9'bxx_xx_xxxxx; // []
L[2020] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[2021] = 9'b10_01_00011; // ['ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->']
L[2022] = 9'bxx_xx_xxxxx; // []
L[2023] = 9'bxx_xx_xxxxx; // []
L[2024] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[2025] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[2026] = 9'b01_00_01000; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[2027] = 9'bxx_xx_xxxxx; // []
L[2028] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[2029] = 9'b10_01_00010; // ['ALU([AX])->A', 'ALU([AX])->?']
L[2030] = 9'bxx_xx_xxxxx; // []
L[2031] = 9'bxx_xx_xxxxx; // []
L[2032] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[2033] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[2034] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[2035] = 9'bxx_xx_xxxxx; // []
L[2036] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[2037] = 9'b00_01_00011; // [AX]->T
L[2038] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[2039] = 9'b10_01_00101; // T->[AX]
L[2040] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[2041] = 9'b00_00_00000; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T']
L[2042] = 9'b11_00_01000; // ['[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+Y->AL']
L[2043] = 9'bxx_xx_xxxxx; // []
L[2044] = 9'b00_01_01001; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
L[2045] = 9'b00_01_00011; // [AX]->T
L[2046] = 9'b00_01_00100; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
L[2047] = 9'b10_01_00101; // T->[AX]
  end  
  always @(posedge clk) if (reset) begin
    M <= 0; // Stupid XILINX inferral only allows 0 as reset value.
  end else if (ce) begin
    M <= L[{IR, State}];    
  end
endmodule

module MicroCodeTable(input clk, input ce, input reset, input [7:0] IR, input [2:0] State, output [37:0] Mout);
  wire [8:0] M;
  MicroCodeTableInner inner(clk, ce, reset, IR, State, M);
  reg [14:0] A[0:31];
  reg [18:0] B[0:255];
  initial begin
A[0] = 15'b_10__0_10101_0xx_01_00; // ['[PC++]', '[PC++]->AL', '[PC++]->?', '[PC++]->T', 'PC+1->PC', '']
A[1] = 15'b_xx__0_0xx11_0xx_01_00; // [PC++]->AH
A[2] = 15'b_xx__1_00000_0xx_00_00; // ['ALU([AX])->A', 'ALU([AX])->?', '[PC]->,ALU()->A', 'Setappropriateflags', 'ALU([SP])->A', '[SP]->P', 'ALU()->X,Y', 'ALU()->A']
A[3] = 15'b_10__0_00000_0xx_00_00; // ['[AX]->T', 'ALU([AX])->?', 'ALU([AX])->A', 'ALU([AX])->', '[PC]->', 'NO-OP', '[VECT]->T', '']
A[4] = 15'b_11__1_00000_100_00_00; // ['T->[AX],ALU(T)->T', 'T->[AX],ALU(T)->T:A']
A[5] = 15'b_xx__0_xxxxx_100_00_00; // T->[AX]
A[6] = 15'b_xx__0_00000_101_00_00; // ALU()->[AX]
A[7] = 15'b_0x__0_10000_0xx_00_00; // ['[AX]->?,AL+X->AL', '[AX]->?,AL+X/Y->AL', 'KEEP_AC']
A[8] = 15'b_xx__0_10011_0xx_01_00; // ['[PC++]->AH,AL+X/Y->AL', '[PC++]->AH,AL+X->AL', '[PC++]->AH,AL+Y->AL']
A[9] = 15'b_10__0_0xx10_0xx_00_00; // ['[AX]->?,AH+FIX->AH', '[AX]->T,AH+FIX->AH']
A[10] = 15'b_10__0_11000_0xx_00_00; // [AX]->T,AL+1->AL
A[11] = 15'b_xx__0_11111_0xx_00_00; // [AX]->AH,T->AL
A[12] = 15'b_xx__0_10011_0xx_00_00; // [AX]->AH,T+Y->AL
A[13] = 15'b_xx__1_xxxxx_0xx_01_00; // ['ALU([PC++])->A', 'ALU([PC++])->?', 'ALU([PC++])->Reg']
A[14] = 15'b_xx__0_xxxxx_101_00_11; // ALU(A)->[SP--]
A[15] = 15'b_xx__0_xxxxx_110_00_11; // P->[SP--]
A[16] = 15'b_10__0_xxxxx_0xx_00_10; // ['SP++', 'SP+1->SP', '[SP]->T,SP+1->SP']
A[17] = 15'b_xx__0_xxxxx_0xx_11_00; // PC+T->PC
A[18] = 15'b_xx__0_xxxxx_0xx_00_01; // X->S
A[19] = 15'b_xx__0_xxxxx_0xx_10_00; // ['[PC]:T->PC', '[AX]:T->PC', '[VECT]:T->PC', '[SP]:T->PC']
A[20] = 15'b_0x__0_xxxxx_111_00_11; // ['PCH->[SP--]', 'PCL->[SP--],', 'PCH->[SP--](KEEPAC)', 'PCL->[SP--](KEEPAC)']
A[21] = 15'b_xx__1_xxxxx_110_00_11; // P->[SP--]
A[22] = 15'b_xx__1_xxxxx_0xx_00_10; // [SP]->P,SP+1->SP
A[23] = 15'b_xx__x_xxxxx_xxx_xx_xx; // []
A[24] = 15'b_xx__x_xxxxx_xxx_xx_xx; // []
A[25] = 15'b_xx__x_xxxxx_xxx_xx_xx; // []
A[26] = 15'b_xx__x_xxxxx_xxx_xx_xx; // []
A[27] = 15'b_xx__x_xxxxx_xxx_xx_xx; // []
A[28] = 15'b_xx__x_xxxxx_xxx_xx_xx; // []
A[29] = 15'b_xx__x_xxxxx_xxx_xx_xx; // []
A[30] = 15'b_xx__x_xxxxx_xxx_xx_xx; // []
A[31] = 15'b_xx__x_xxxxx_xxx_xx_xx; // []
B[0] = 19'bxxxxxxxxxx0_000_00_010;
B[32] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[64] = 19'bxxxxxxxxxx0_000_00_100;
B[96] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[128] = 19'b011010x10x0_xxx_00_xxx;
B[160] = 19'bxx0010x10x0_100_00_001;
B[192] = 19'b010010x1100_000_00_001;
B[224] = 19'b100010x1100_000_00_001;
B[1] = 19'b000010x0001_010_00_001;
B[33] = 19'b000010x0011_010_00_001;
B[65] = 19'b000010x0101_010_00_001;
B[97] = 19'b000010x0111_010_00_001;
B[129] = 19'b001010x10x1_xxx_00_xxx;
B[161] = 19'bxx0010x10x1_010_00_001;
B[193] = 19'b000010x1101_000_00_001;
B[225] = 19'b000010x1111_010_00_001;
B[2] = 19'bxx0100010x0_000_00_001;
B[34] = 19'bxx0100110x0_000_00_001;
B[66] = 19'bxx0101010x0_000_00_001;
B[98] = 19'bxx0101110x0_000_00_001;
B[130] = 19'b101010x10x0_xxx_00_xxx;
B[162] = 19'bxx0010x10x0_001_00_001;
B[194] = 19'bxx0111010x0_000_00_001;
B[226] = 19'bxx0111110x0_000_00_001;
B[3] = 19'b00010000001_010_00_001;
B[35] = 19'b00010010011_010_00_001;
B[67] = 19'b00010100101_010_00_001;
B[99] = 19'b00010110111_010_00_001;
B[131] = 19'b111010x10x1_xxx_00_xxx;
B[163] = 19'bxx0010x10x1_011_00_001;
B[195] = 19'b00011101101_000_00_001;
B[227] = 19'b00011111111_010_00_001;
B[4] = 19'b000010x0000_xxx_00_xxx;
B[36] = 19'b000010x0010_000_00_001;
B[68] = 19'b000010x0100_xxx_00_xxx;
B[100] = 19'b000010x0110_xxx_00_xxx;
B[132] = 19'b011010x10x0_xxx_00_xxx;
B[164] = 19'bxx0010x10x0_100_00_001;
B[196] = 19'b010010x1100_000_00_001;
B[228] = 19'b100010x1100_000_00_001;
B[5] = 19'b000010x0001_010_00_001;
B[37] = 19'b000010x0011_010_00_001;
B[69] = 19'b000010x0101_010_00_001;
B[101] = 19'b000010x0111_010_00_001;
B[133] = 19'b001010x10x1_xxx_00_xxx;
B[165] = 19'bxx0010x10x1_010_00_001;
B[197] = 19'b000010x1101_000_00_001;
B[229] = 19'b000010x1111_010_00_001;
B[6] = 19'bxx0100010x0_000_00_001;
B[38] = 19'bxx0100110x0_000_00_001;
B[70] = 19'bxx0101010x0_000_00_001;
B[102] = 19'bxx0101110x0_000_00_001;
B[134] = 19'b101010x10x0_xxx_00_xxx;
B[166] = 19'bxx0010x10x0_001_00_001;
B[198] = 19'bxx0111010x0_000_00_001;
B[230] = 19'bxx0111110x0_000_00_001;
B[7] = 19'b00010000001_010_00_001;
B[39] = 19'b00010010011_010_00_001;
B[71] = 19'b00010100101_010_00_001;
B[103] = 19'b00010110111_010_00_001;
B[135] = 19'b111010x10x1_xxx_00_xxx;
B[167] = 19'bxx0010x10x1_011_00_001;
B[199] = 19'b00011101101_000_00_001;
B[231] = 19'b00011111111_010_00_001;
B[8] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[40] = 19'bxxxxxxxxxx0_000_00_100;
B[72] = 19'b001010x10x0_xxx_00_xxx;
B[104] = 19'bxx0010x10x0_010_00_001;
B[136] = 19'b011011010x0_100_00_001;
B[168] = 19'b001010x10x0_100_00_001;
B[200] = 19'b011011110x0_100_00_001;
B[232] = 19'b101011110x0_001_00_001;
B[9] = 19'b000010x0001_010_00_001;
B[41] = 19'b000010x0011_010_00_001;
B[73] = 19'b000010x0101_010_00_001;
B[105] = 19'b000010x0111_010_00_001;
B[137] = 19'b001010x10x1_xxx_00_xxx;
B[169] = 19'bxx0010x10x1_010_00_001;
B[201] = 19'b000010x1101_000_00_001;
B[233] = 19'b000010x1111_010_00_001;
B[10] = 19'b001000010x0_010_00_001;
B[42] = 19'b001000110x0_010_00_001;
B[74] = 19'b001001010x0_010_00_001;
B[106] = 19'b001001110x0_010_00_001;
B[138] = 19'b101010x10x0_010_00_001;
B[170] = 19'b001010x10x0_001_00_001;
B[202] = 19'b101011010x0_001_00_001;
B[234] = 19'bxx0111110x0_000_00_001;
B[11] = 19'b000010x0001_010_00_001;
B[43] = 19'b000010x0011_010_00_001;
B[75] = 19'b000010x0101_010_00_001;
B[107] = 19'b000010x0111_010_00_001;
B[139] = 19'b111010x10x1_xxx_00_xxx;
B[171] = 19'bxx0010x10x1_011_00_001;
B[203] = 19'b000010x1101_000_00_001;
B[235] = 19'b000010x1111_010_00_001;
B[12] = 19'b000010x0000_xxx_00_xxx;
B[44] = 19'b000010x0010_000_00_001;
B[76] = 19'bxxxxxxxxxx0_000_00_001;
B[108] = 19'bxxxxxxxxxx0_000_00_001;
B[140] = 19'b011010x10x0_xxx_00_xxx;
B[172] = 19'bxx0010x10x0_100_00_001;
B[204] = 19'b010010x1100_000_00_001;
B[236] = 19'b100010x1100_000_00_001;
B[13] = 19'b000010x0001_010_00_001;
B[45] = 19'b000010x0011_010_00_001;
B[77] = 19'b000010x0101_010_00_001;
B[109] = 19'b000010x0111_010_00_001;
B[141] = 19'b001010x10x1_xxx_00_xxx;
B[173] = 19'bxx0010x10x1_010_00_001;
B[205] = 19'b000010x1101_000_00_001;
B[237] = 19'b000010x1111_010_00_001;
B[14] = 19'bxx0100010x0_000_00_001;
B[46] = 19'bxx0100110x0_000_00_001;
B[78] = 19'bxx0101010x0_000_00_001;
B[110] = 19'bxx0101110x0_000_00_001;
B[142] = 19'b101010x10x0_xxx_00_xxx;
B[174] = 19'bxx0010x10x0_001_00_001;
B[206] = 19'bxx0111010x0_000_00_001;
B[238] = 19'bxx0111110x0_000_00_001;
B[15] = 19'b00010000001_010_00_001;
B[47] = 19'b00010010011_010_00_001;
B[79] = 19'b00010100101_010_00_001;
B[111] = 19'b00010110111_010_00_001;
B[143] = 19'b111010x10x1_xxx_00_xxx;
B[175] = 19'bxx0010x10x1_011_00_001;
B[207] = 19'b00011101101_000_00_001;
B[239] = 19'b00011111111_010_00_001;
B[16] = 19'bxxxxxxxxxx0_xxx_11_xxx;
B[48] = 19'bxxxxxxxxxx0_xxx_11_xxx;
B[80] = 19'bxxxxxxxxxx0_xxx_11_xxx;
B[112] = 19'bxxxxxxxxxx0_xxx_11_xxx;
B[144] = 19'b011010x10x0_xxx_11_xxx;
B[176] = 19'bxx0010x10x0_xxx_11_xxx;
B[208] = 19'bxxxxxxxxxx0_xxx_11_xxx;
B[240] = 19'bxxxxxxxxxx0_xxx_11_xxx;
B[17] = 19'b000010x0001_010_11_001;
B[49] = 19'b000010x0011_010_11_001;
B[81] = 19'b000010x0101_010_11_001;
B[113] = 19'b000010x0111_010_11_001;
B[145] = 19'b001010x10x1_xxx_11_xxx;
B[177] = 19'bxx0010x10x1_010_11_001;
B[209] = 19'b000010x1101_000_11_001;
B[241] = 19'b000010x1111_010_11_001;
B[18] = 19'bxx0100010x0_000_11_001;
B[50] = 19'bxx0100110x0_000_11_001;
B[82] = 19'bxx0101010x0_000_11_001;
B[114] = 19'bxx0101110x0_000_11_001;
B[146] = 19'b101010x10x0_xxx_11_xxx;
B[178] = 19'bxx0010x10x0_xxx_11_xxx;
B[210] = 19'bxx0111010x0_000_11_001;
B[242] = 19'bxx0111110x0_000_11_001;
B[19] = 19'b00010000001_010_11_001;
B[51] = 19'b00010010011_010_11_001;
B[83] = 19'b00010100101_010_11_001;
B[115] = 19'b00010110111_010_11_001;
B[147] = 19'b111010x10x1_xxx_11_xxx;
B[179] = 19'bxx0010x10x1_011_11_001;
B[211] = 19'b00011101101_000_11_001;
B[243] = 19'b00011111111_010_11_001;
B[20] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[52] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[84] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[116] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[148] = 19'b011010x10x0_xxx_00_xxx;
B[180] = 19'bxx0010x10x0_100_00_001;
B[212] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[244] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[21] = 19'b000010x0001_010_00_001;
B[53] = 19'b000010x0011_010_00_001;
B[85] = 19'b000010x0101_010_00_001;
B[117] = 19'b000010x0111_010_00_001;
B[149] = 19'b001010x10x1_xxx_00_xxx;
B[181] = 19'bxx0010x10x1_010_00_001;
B[213] = 19'b000010x1101_000_00_001;
B[245] = 19'b000010x1111_010_00_001;
B[22] = 19'bxx0100010x0_000_00_001;
B[54] = 19'bxx0100110x0_000_00_001;
B[86] = 19'bxx0101010x0_000_00_001;
B[118] = 19'bxx0101110x0_000_00_001;
B[150] = 19'b101010x10x0_xxx_10_xxx;
B[182] = 19'bxx0010x10x0_001_10_001;
B[214] = 19'bxx0111010x0_000_00_001;
B[246] = 19'bxx0111110x0_000_00_001;
B[23] = 19'b00010000001_010_00_001;
B[55] = 19'b00010010011_010_00_001;
B[87] = 19'b00010100101_010_00_001;
B[119] = 19'b00010110111_010_00_001;
B[151] = 19'b111010x10x1_xxx_10_xxx;
B[183] = 19'bxx0010x10x1_011_10_001;
B[215] = 19'b00011101101_000_00_001;
B[247] = 19'b00011111111_010_00_001;
B[24] = 19'bxxxxxxxxxx0_000_10_101;
B[56] = 19'bxxxxxxxxxx0_000_10_101;
B[88] = 19'bxxxxxxxxxx0_000_10_110;
B[120] = 19'bxxxxxxxxxx0_000_10_110;
B[152] = 19'b011010x10x0_010_10_001;
B[184] = 19'bxx1110x10x0_000_10_011;
B[216] = 19'bxxxxxxxxxx0_000_10_111;
B[248] = 19'bxxxxxxxxxx0_000_10_111;
B[25] = 19'b000010x0001_010_10_001;
B[57] = 19'b000010x0011_010_10_001;
B[89] = 19'b000010x0101_010_10_001;
B[121] = 19'b000010x0111_010_10_001;
B[153] = 19'b001010x10x1_xxx_10_xxx;
B[185] = 19'bxx0010x10x1_010_10_001;
B[217] = 19'b000010x1101_000_10_001;
B[249] = 19'b000010x1111_010_10_001;
B[26] = 19'bxx0100010x0_000_10_001;
B[58] = 19'bxx0100110x0_000_10_001;
B[90] = 19'bxx0101010x0_000_10_001;
B[122] = 19'bxx0101110x0_000_10_001;
B[154] = 19'b101010x10x0_xxx_10_xxx;
B[186] = 19'bxx1110x10x0_001_10_001;
B[218] = 19'bxx0111010x0_000_10_001;
B[250] = 19'bxx0111110x0_000_10_001;
B[27] = 19'b00010000001_010_10_001;
B[59] = 19'b00010010011_010_10_001;
B[91] = 19'b00010100101_010_10_001;
B[123] = 19'b00010110111_010_10_001;
B[155] = 19'b111010x10x1_xxx_10_xxx;
B[187] = 19'bxx0010x10x1_xxx_10_xxx;
B[219] = 19'b00011101101_000_10_001;
B[251] = 19'b00011111111_010_10_001;
B[28] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[60] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[92] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[124] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[156] = 19'b011010x10x0_xxx_00_xxx;
B[188] = 19'bxx0010x10x0_100_00_001;
B[220] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[252] = 19'bxxxxxxxxxx0_xxx_00_xxx;
B[29] = 19'b000010x0001_010_00_001;
B[61] = 19'b000010x0011_010_00_001;
B[93] = 19'b000010x0101_010_00_001;
B[125] = 19'b000010x0111_010_00_001;
B[157] = 19'b001010x10x1_xxx_00_xxx;
B[189] = 19'bxx0010x10x1_010_00_001;
B[221] = 19'b000010x1101_000_00_001;
B[253] = 19'b000010x1111_010_00_001;
B[30] = 19'bxx0100010x0_000_00_001;
B[62] = 19'bxx0100110x0_000_00_001;
B[94] = 19'bxx0101010x0_000_00_001;
B[126] = 19'bxx0101110x0_000_00_001;
B[158] = 19'b101010x10x0_xxx_10_xxx;
B[190] = 19'bxx0010x10x0_001_10_001;
B[222] = 19'bxx0111010x0_000_00_001;
B[254] = 19'bxx0111110x0_000_00_001;
B[31] = 19'b00010000001_010_00_001;
B[63] = 19'b00010010011_010_00_001;
B[95] = 19'b00010100101_010_00_001;
B[127] = 19'b00010110111_010_00_001;
B[159] = 19'b111010x10x1_xxx_10_xxx;
B[191] = 19'bxx0010x10x1_011_10_001;
B[223] = 19'b00011101101_000_00_001;
B[255] = 19'b00011111111_010_00_001;
  end  
  wire [14:0] R = A[M[4:0]];
  reg [18:0] AluFlags;
  always @(posedge clk) if (reset) begin
    AluFlags <= 0;
  end else if (ce) begin  
    AluFlags <= B[IR];
  end

  assign Mout = {AluFlags,// 19
                 M[8:7],  // NextState // 2
                 R[14:13],// LoadT     // 2
                 R[12],   // FlagCtrl  // 1
                 R[11:7], // AddrCtrl  // 5
                 R[6:4],  // MemWrite  // 3
                 M[6:5],  // AddrBus   // 2
                 R[3:2],  // LoadPC    // 2
                 R[1:0]   // LoadSP    // 2
                 };
endmodule

module sigma_delta_dac(
   output    reg             DACout,   //Average Output feeding analog lowpass
   input          [MSBI:0]    DACin,   //DAC input (excess 2**MSBI)
   input                  CLK,
   input                  CEN,
   input                   RESET
);

parameter MSBI = 7;

reg [MSBI+2:0] DeltaAdder;   //Output of Delta Adder
reg [MSBI+2:0] SigmaAdder;   //Output of Sigma Adder
reg [MSBI+2:0] SigmaLatch;   //Latches output of Sigma Adder
reg [MSBI+2:0] DeltaB;      //B input of Delta Adder

always @ (*)
   DeltaB = {SigmaLatch[MSBI+2], SigmaLatch[MSBI+2]} << (MSBI+1);

always @(*)
   DeltaAdder = DACin + DeltaB;
   
always @(*)
   SigmaAdder = DeltaAdder + SigmaLatch;
   
always @(posedge CLK)
    begin
      SigmaLatch <= SigmaAdder;
      DACout <= SigmaLatch[MSBI+2];
   end
endmodule // Copyright (c) 2012-2013 Ludvig Strigeus
// Copyright (c) 2017 David Shah
// This program is GPL Licensed. See COPYING for the full license.

`timescale 1ns / 1ps

module top (  
	// clock input
  input clock_16,
  output LED0, LED1,
  
  // VGA
  output         VGA_HS, // VGA H_SYNC
  output         VGA_VS, // VGA V_SYNC
  output [ 3:0]  VGA_R, // VGA Red[3:0]
  output [ 3:0]  VGA_G, // VGA Green[3:0]
  output [ 3:0]  VGA_B, // VGA Blue[3:0]
                                                                                                    

  // audio
  output           AUDIO_O,
  
  // joystick
  output joy_strobe, joy_clock,
  input joy_data,
  
  // flashmem
  output flash_sck,
  output flash_csn,
  output flash_mosi,
  input flash_miso,
  
  input [4:0] buttons
  
);
	wire clock;

wire [4:0] sel_btn;

`ifdef no_io_prim
assign sel_btn = buttons;
`else
//Use SB_IO so we can enable pullup
(* PULLUP_RESISTOR = "10K" *)
SB_IO #(
  .PIN_TYPE(6'b000001),
  .PULLUP(1'b1)
) btns [4:0]   (
  .PACKAGE_PIN(buttons),
  .D_IN_0(sel_btn)
);
`endif

  wire scandoubler_disable;

  wire clock_locked;
  wire locked_pre;
  always @(posedge clock)
    clock_locked <= locked_pre;
  
  wire [8:0] cycle;
  wire [8:0] scanline;
  wire [15:0] sample;
  wire [5:0] color;
  
  wire load_done;
  wire [21:0] memory_addr;
  wire memory_read_cpu, memory_read_ppu;
  wire memory_write;
  wire [7:0] memory_din_cpu, memory_din_ppu;
  wire [7:0] memory_dout;
  
  wire [31:0] mapper_flags;
  
  pll pll_i (
  	.clock_in(clock_16),
  	.clock_out(clock),
  	.locked(locked_pre)
  );  
  
  assign LED0 = memory_addr[0];
  assign LED1 = !load_done;
  
  wire sys_reset = !clock_locked;
  reg reload;
  reg [2:0] last_pressed;
  reg [3:0] btn_dly;
  always @ ( posedge clock ) begin
    //Detect button release and trigger reload
    btn_dly <= sel_btn[3:0];
    if (sel_btn[3:0] == 4'b1111 && btn_dly != 4'b1111)
      reload <= 1'b1;
    else
      reload <= 1'b0;
    // Button 4 is a "shift"
    if(!sel_btn[0])
      last_pressed <= {!sel_btn[4], 2'b00};
    else if(!sel_btn[1])
      last_pressed <= {!sel_btn[4], 2'b01};
    else if(!sel_btn[2])
      last_pressed <= {!sel_btn[4], 2'b10};
    else if(!sel_btn[3])
      last_pressed <= {!sel_btn[4], 2'b11};
  end
  
  main_mem mem (
    .clock(clock),
    .reset(sys_reset),
    .reload(reload),
    .index({1'b0, last_pressed}),
    .load_done(load_done),
    .flags_out(mapper_flags),
    //NES interface
    .mem_addr(memory_addr),
    .mem_rd_cpu(memory_read_cpu),
    .mem_rd_ppu(memory_read_ppu),
    .mem_wr(memory_write),
    .mem_q_cpu(memory_din_cpu),
    .mem_q_ppu(memory_din_ppu),
    .mem_d(memory_dout),
    
    //Flash load interface
    .flash_csn(flash_csn),
    .flash_sck(flash_sck),
    .flash_mosi(flash_mosi),
    .flash_miso(flash_miso)
  );
  
  wire reset_nes = !load_done || sys_reset;
  reg [1:0] nes_ce;
  wire run_nes = (nes_ce == 3);	// keep running even when reset, so that the reset can actually do its job!
  
  wire run_nes_g;
  SB_GB ce_buf (
    .USER_SIGNAL_TO_GLOBAL_BUFFER(run_nes),
    .GLOBAL_BUFFER_OUTPUT(run_nes_g)
  );
  
  // NES is clocked at every 4th cycle.
  always @(posedge clock)
    nes_ce <= nes_ce + 1;
  
  wire [31:0] dbgadr;
  wire [1:0] dbgctr;
  
  NES nes(clock, reset_nes, run_nes_g,
          mapper_flags,
          sample, color,
          joy_strobe, joy_clock, {3'b0,!joy_data},
          5'b11111,  // enable all channels
          memory_addr,
          memory_read_cpu, memory_din_cpu,
          memory_read_ppu, memory_din_ppu,
          memory_write, memory_dout,
          cycle, scanline,
          dbgadr,
          dbgctr);


video video (
	.clk(clock),
		
	.color(color),
	.count_v(scanline),
	.count_h(cycle),
	.mode(1'b0),
	.smoothing(1'b1),
	.scanlines(1'b1),
	.overscan(1'b1),
	.palette(1'b0),
	
	.VGA_HS(VGA_HS),
	.VGA_VS(VGA_VS),
	.VGA_R(VGA_R),
	.VGA_G(VGA_G),
	.VGA_B(VGA_B)
	
);

wire audio;
assign AUDIO_O = audio;
/*sigma_delta_dac sigma_delta_dac (
	.DACout(audio),
	.DACin(sample[15:8]),
	.CLK(clock),
	.RESET(reset_nes),
  .CEN(run_nes)
);*/



endmodule
// Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.

// No mapper chip
module MMC0(input clk, input ce,
            input [31:0] flags,
            input [15:0] prg_ain, output [21:0] prg_aout,
            input prg_read, prg_write,                   // Read / write signals
            input [7:0] prg_din,
            output prg_allow,                            // Enable access to memory for the specified operation.
            input [13:0] chr_ain, output [21:0] chr_aout,
            output chr_allow,                      // Allow write
            output vram_a10,                             // Value for A10 address line
            output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.
  assign prg_aout = {7'b00_0000_0, prg_ain[14:0]};
  assign prg_allow = prg_ain[15] && !prg_write;
  assign chr_allow = flags[15];
  assign chr_aout = {9'b10_0000_000, chr_ain[12:0]};
  assign vram_ce = chr_ain[13];
  assign vram_a10 = flags[14] ? chr_ain[10] : chr_ain[11];
endmodule

// MMC1 mapper chip. Maps prg or chr addresses into a linear address.
// If vram_ce is set, {vram_a10, chr_aout[9:0]} are used to access the NES internal VRAM instead.
module MMC1(input clk, input ce, input reset,
            input [31:0] flags,
            input [15:0] prg_ain, output [21:0] prg_aout,
            input prg_read, prg_write,                   // Read / write signals
            input [7:0] prg_din,
            output prg_allow,                            // Enable access to memory for the specified operation.
            input [13:0] chr_ain, output [21:0] chr_aout,
            output chr_allow,                      // Allow write
            output vram_a10,                             // Value for A10 address line
            output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.
  reg [4:0] shift;
  
// CPPMM
// |||||
// |||++- Mirroring (0: one-screen, lower bank; 1: one-screen, upper bank;
// |||               2: vertical; 3: horizontal)
// |++--- PRG ROM bank mode (0, 1: switch 32 KB at $8000, ignoring low bit of bank number;
// |                         2: fix first bank at $8000 and switch 16 KB bank at $C000;
// |                         3: fix last bank at $C000 and switch 16 KB bank at $8000)
// +----- CHR ROM bank mode (0: switch 8 KB at a time; 1: switch two separate 4 KB banks)
  reg [4:0] control;

// CCCCC
// |||||
// +++++- Select 4 KB or 8 KB CHR bank at PPU $0000 (low bit ignored in 8 KB mode)
  reg [4:0] chr_bank_0;

// CCCCC
// |||||
// +++++- Select 4 KB CHR bank at PPU $1000 (ignored in 8 KB mode)
  reg [4:0] chr_bank_1;
  
// RPPPP
// |||||
// |++++- Select 16 KB PRG ROM bank (low bit ignored in 32 KB mode)
// +----- PRG RAM chip enable (0: enabled; 1: disabled; ignored on MMC1A)
  reg [4:0] prg_bank;

  reg delay_ctrl;	// used to prevent fast-write to the control register

  wire [2:0] prg_size = flags[10:8];
   
  // Update shift register
  always @(posedge clk) if (reset) begin
		shift <= 5'b10000;
		control <= 5'b0_11_00;
		chr_bank_0 <= 0;
		chr_bank_1 <= 0;
		prg_bank <= 5'b00000;
		delay_ctrl <= 0;
  end else if (ce) begin
    if (!prg_write)
		delay_ctrl <= 1'b0;
    if (prg_write && prg_ain[15] && !delay_ctrl) begin
	   delay_ctrl <= 1'b1;
      if (prg_din[7]) begin
        shift <= 5'b10000;
        control <= control | 5'b0_11_00;
//        $write("MMC1 RESET!\n");
      end else begin
        if (shift[0]) begin
//          $write("MMC1 WRITE %X to %X!\n", {prg_din[0], shift[4:1]}, prg_ain);
          casez(prg_ain[14:13])
          0: control    <= {prg_din[0], shift[4:1]};
          1: chr_bank_0 <= {prg_din[0], shift[4:1]};
          2: chr_bank_1 <= {prg_din[0], shift[4:1]};
          3: prg_bank   <= {prg_din[0], shift[4:1]};
          endcase
          shift <= 5'b10000;
        end else begin
          shift <= {prg_din[0], shift[4:1]};
        end
      end
    end
  end
  
  // The PRG bank to load. Each increment here is 16kb. So valid values are 0..15.
  // prg_ain[14] selects bank0 ($8000) or bank1 ($C000)
  reg [3:0] prgsel;  
  always @* begin
    casez({control[3:2], prg_ain[14]})
    3'b0?_?: prgsel = {prg_bank[3:1], prg_ain[14]};	// Swap 32Kb
    3'b10_0: prgsel = 4'b0000;								// Swap 16Kb at $C000 with access at $8000, so select page 0 (hardcoded)
    3'b10_1: prgsel = prg_bank[3:0];						// Swap 16Kb at $C000 with $C000 access, so select page based on prg_bank (register 3)
    3'b11_0: prgsel = prg_bank[3:0];						// Swap 16Kb at $8000 with $8000 access, so select page based on prg_bank (register 3)
    3'b11_1: prgsel = 4'b1111;								// Swap 16Kb at $8000 with $C000 access, so select last page (hardcoded)
    endcase
  end
  
  // The CHR bank to load. Each increment here is 4 kb. So valid values are 0..31.
  reg [4:0] chrsel;
  always @* begin
    casez({control[4], chr_ain[12]})
    2'b0_?: chrsel = {chr_bank_0[4:1], chr_ain[12]};
    2'b1_0: chrsel = chr_bank_0;
    2'b1_1: chrsel = chr_bank_1;
    endcase
  end
  assign chr_aout = {5'b100_00, chrsel, chr_ain[11:0]};
  wire [21:0] prg_aout_tmp = prg_size == 5 ? {3'b000, chrsel[4], prgsel, prg_ain[13:0]}	// for large PRG ROM, CHR A16 selects the 256KB PRG bank
														 : {4'b00_00, prgsel, prg_ain[13:0]};
  
  // The a10 VRAM address line. (Used for mirroring)
  reg vram_a10_t;
  always @* begin
    casez(control[1:0])
    2'b00: vram_a10_t = 0;             // One screen, lower bank
    2'b01: vram_a10_t = 1;             // One screen, upper bank
    2'b10: vram_a10_t = chr_ain[10];   // One screen, vertical
    2'b11: vram_a10_t = chr_ain[11];   // One screen, horizontal
    endcase
  end
  assign vram_a10 = vram_a10_t;
  assign vram_ce = chr_ain[13];
  
  wire prg_is_ram = prg_ain >= 'h6000 && prg_ain < 'h8000;
  assign prg_allow = prg_ain[15] && !prg_write || prg_is_ram;
  wire [21:0] prg_ram = {9'b11_1100_000, prg_ain[12:0]};
  
  assign prg_aout = prg_is_ram ? prg_ram : prg_aout_tmp;
  assign chr_allow = flags[15];
endmodule

// MMC2 mapper chip. PRG ROM: 128kB. Bank Size: 8kB. CHR ROM: 128kB
module MMC2(input clk, input ce, input reset,
            input [31:0] flags,
            input [15:0] prg_ain, output [21:0] prg_aout,
            input prg_read, prg_write,                   // Read / write signals
            input [7:0] prg_din,
            output prg_allow,                            // Enable access to memory for the specified operation.
            input chr_read, input [13:0] chr_ain, output [21:0] chr_aout,
            output chr_allow,                      // Allow write
            output vram_a10,                             // Value for A10 address line
            output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.

// PRG ROM bank select ($A000-$AFFF)
// 7  bit  0
// ---- ----
// xxxx PPPP
//      ||||
//      ++++- Select 8 KB PRG ROM bank for CPU $8000-$9FFF
  reg [3:0] prg_bank;

// CHR ROM $FD/0000 bank select ($B000-$BFFF)
// 7  bit  0
// ---- ----
// xxxC CCCC
//    | ||||
//    +-++++- Select 4 KB CHR ROM bank for PPU $0000-$0FFF
//            used when latch 0 = $FD
  reg   [4:0] chr_bank_0a;

// CHR ROM $FE/0000 bank select ($C000-$CFFF)
// 7  bit  0
// ---- ----
// xxxC CCCC
//    | ||||
//    +-++++- Select 4 KB CHR ROM bank for PPU $0000-$0FFF
//            used when latch 0 = $FE
   reg [4:0] chr_bank_0b;
   
// CHR ROM $FD/1000 bank select ($D000-$DFFF)
// 7  bit  0
// ---- ----
// xxxC CCCC
//    | ||||
//    +-++++- Select 4 KB CHR ROM bank for PPU $1000-$1FFF
//            used when latch 1 = $FD
  reg [4:0] chr_bank_1a;
   
// CHR ROM $FE/1000 bank select ($E000-$EFFF)
// 7  bit  0
// ---- ----
// xxxC CCCC
//    | ||||
//    +-++++- Select 4 KB CHR ROM bank for PPU $1000-$1FFF
//            used when latch 1 = $FE
  reg [4:0] chr_bank_1b; 
  
// Mirroring ($F000-$FFFF)
// 7  bit  0
// ---- ----
// xxxx xxxM
//         |
//         +- Select nametable mirroring (0: vertical; 1: horizontal)  
  reg mirroring;
  
  reg latch_0, latch_1;
	
  // Update registers
  always @(posedge clk) if (ce) begin
    if (prg_write && prg_ain[15]) begin
      case(prg_ain[14:12])
      2: prg_bank <= prg_din[3:0];     // $A000
      3: chr_bank_0a <= prg_din[4:0];  // $B000
      4: chr_bank_0b <= prg_din[4:0];  // $C000
      5: chr_bank_1a <= prg_din[4:0];  // $D000
      6: chr_bank_1b <= prg_din[4:0];  // $E000
      7: mirroring <=  prg_din[0];     // $F000
      endcase
    end
  end
  
// PPU reads $0FD8: latch 0 is set to $FD for subsequent reads
// PPU reads $0FE8: latch 0 is set to $FE for subsequent reads
// PPU reads $1FD8 through $1FDF: latch 1 is set to $FD for subsequent reads
// PPU reads $1FE8 through $1FEF: latch 1 is set to $FE for subsequent reads
  always @(posedge clk) if (ce && chr_read) begin
    latch_0 <= (chr_ain & 14'h3fff) == 14'h0fd8 ? 0 : (chr_ain & 14'h3fff) == 14'h0fe8 ? 1 : latch_0;
    latch_1 <= (chr_ain & 14'h3ff8) == 14'h1fd8 ? 0 : (chr_ain & 14'h3ff8) == 14'h1fe8 ? 1 : latch_1;
  end
  
  // The PRG bank to load. Each increment here is 8kb. So valid values are 0..15.
  reg [3:0] prgsel;
  always @* begin
    casez(prg_ain[14:13])
    2'b00:   prgsel = prg_bank;
    default: prgsel = {2'b11, prg_ain[14:13]};
    endcase
  end
  assign prg_aout = {5'b00_000, prgsel, prg_ain[12:0]};

  // The CHR bank to load. Each increment here is 4kb. So valid values are 0..31.
  reg [4:0] chrsel;
  always @* begin
    casez({chr_ain[12], latch_0, latch_1})
    3'b00?: chrsel = chr_bank_0a;
    3'b01?: chrsel = chr_bank_0b;
    3'b1?0: chrsel = chr_bank_1a;
    3'b1?1: chrsel = chr_bank_1b;
    endcase
  end
  assign chr_aout = {5'b100_00, chrsel, chr_ain[11:0]};
  
  // The a10 VRAM address line. (Used for mirroring)
  assign vram_a10 = mirroring ? chr_ain[11] : chr_ain[10];
  assign vram_ce = chr_ain[13];
  
  assign prg_allow = prg_ain[15] && !prg_write;
  assign chr_allow = flags[15];
endmodule

// This mapper also handles mapper 47,118,119 and 206.
module MMC3(input clk, input ce, input reset,
            input [31:0] flags,
            input [15:0] prg_ain, output [21:0] prg_aout,
            input prg_read, prg_write,                   // Read / write signals
            input [7:0] prg_din,
            output prg_allow,                            // Enable access to memory for the specified operation.
            input [13:0] chr_ain, output [21:0] chr_aout,
            output chr_allow,                            // Allow write
            output vram_a10,                             // Value for A10 address line
            output vram_ce,                              // True if the address should be routed to the internal 2kB VRAM.
            output reg irq);
  reg [2:0] bank_select;             // Register to write to next
  reg prg_rom_bank_mode;             // Mode for PRG banking
  reg chr_a12_invert;                // Mode for CHR banking
  reg mirroring;                     // 0 = vertical, 1 = horizontal
  reg irq_enable, irq_reload;        // IRQ enabled, and IRQ reload requested
  reg [7:0] irq_latch, counter;      // IRQ latch value and current counter
  reg ram_enable, ram_protect;       // RAM protection bits
  reg [6:0] chr_bank_0, chr_bank_1;  // Selected CHR banks
  reg [7:0] chr_bank_2, chr_bank_3, chr_bank_4, chr_bank_5;
  reg [5:0] prg_bank_0, prg_bank_1;  // Selected PRG banks
  wire prg_is_ram;
    
  // The alternative behavior has slightly different IRQ counter semantics.
  wire mmc3_alt_behavior = 0;
  
  wire TQROM = (flags[7:0] == 119); 		// TQROM maps 8kB CHR RAM
  wire TxSROM = (flags[7:0] == 118); 		// Connects CHR A17 to CIRAM A10
  wire mapper47 = (flags[7:0] == 47);		// Mapper 47 is a multicart that has 128k for each game. It has no RAM.
  wire DxROM = (flags[7:0] == 206);
  
  wire four_screen_mirroring = flags[16] | DxROM;
  reg mapper47_multicart;
  wire [7:0] new_counter = (counter == 0 || irq_reload) ? irq_latch : counter - 1;
  reg [3:0] a12_ctr; 
   
  always @(posedge clk) if (reset) begin
    irq <= 0;
    bank_select <= 0;
    prg_rom_bank_mode <= 0;
    chr_a12_invert <= 0;
    mirroring <= flags[14];
    {irq_enable, irq_reload} <= 0;
    {irq_latch, counter} <= 0;
    {ram_enable, ram_protect} <= 0;
    {chr_bank_0, chr_bank_1} <= 0;
    {chr_bank_2, chr_bank_3, chr_bank_4, chr_bank_5} <= 0;
    {prg_bank_0, prg_bank_1} <= 0;
    a12_ctr <= 0;
  end else if (ce) begin
    if (prg_write && prg_ain[15]) begin
      case({prg_ain[14], prg_ain[13], prg_ain[0]})
      3'b00_0: {chr_a12_invert, prg_rom_bank_mode, bank_select} <= {prg_din[7], prg_din[6], prg_din[2:0]}; // Bank select ($8000-$9FFE, even)
      3'b00_1: begin // Bank data ($8001-$9FFF, odd)
        case (bank_select) 
        0: chr_bank_0 <= prg_din[7:1];  // Select 2 KB CHR bank at PPU $0000-$07FF (or $1000-$17FF);
        1: chr_bank_1 <= prg_din[7:1];  // Select 2 KB CHR bank at PPU $0800-$0FFF (or $1800-$1FFF);
        2: chr_bank_2 <= prg_din;       // Select 1 KB CHR bank at PPU $1000-$13FF (or $0000-$03FF);
        3: chr_bank_3 <= prg_din;       // Select 1 KB CHR bank at PPU $1400-$17FF (or $0400-$07FF);
        4: chr_bank_4 <= prg_din;       // Select 1 KB CHR bank at PPU $1800-$1BFF (or $0800-$0BFF);
        5: chr_bank_5 <= prg_din;       // Select 1 KB CHR bank at PPU $1C00-$1FFF (or $0C00-$0FFF);
        6: prg_bank_0 <= prg_din[5:0];  // Select 8 KB PRG ROM bank at $8000-$9FFF (or $C000-$DFFF);
        7: prg_bank_1 <= prg_din[5:0];  // Select 8 KB PRG ROM bank at $A000-$BFFF
        endcase
      end
      3'b01_0: mirroring <= prg_din[0];                   // Mirroring ($A000-$BFFE, even)
      3'b01_1: {ram_enable, ram_protect} <= prg_din[7:6]; // PRG RAM protect ($A001-$BFFF, odd)
      3'b10_0: irq_latch <= prg_din;                      // IRQ latch ($C000-$DFFE, even)
      3'b10_1: irq_reload <= 1;                           // IRQ reload ($C001-$DFFF, odd)
      3'b11_0: begin irq_enable <= 0; irq <= 0; end       // IRQ disable ($E000-$FFFE, even)
      3'b11_1: irq_enable <= 1;                           // IRQ enable ($E001-$FFFF, odd)
      endcase
    end
    
    // For Mapper 47
    // $6000-7FFF:  [.... ...B]  Block select
    if (prg_write && prg_is_ram)
      mapper47_multicart <= prg_din[0];
        
    // Trigger IRQ counter on rising edge of chr_ain[12]
    // All MMC3A's and non-Sharp MMC3B's will generate only a single IRQ when $C000 is $00.
    // This is because this version of the MMC3 generates IRQs when the scanline counter is decremented to 0.
    // In addition, writing to $C001 with $C000 still at $00 will result in another single IRQ being generated.
    // In the community, this is known as the "alternate" or "old" behavior.
    // All MMC3C's and Sharp MMC3B's will generate an IRQ on each scanline while $C000 is $00.
    // This is because this version of the MMC3 generates IRQs when the scanline counter is equal to 0.
    // In the community, this is known as the "normal" or "new" behavior.
    if (chr_ain[12] && a12_ctr == 0) begin
      counter <= new_counter;
      if ( (!mmc3_alt_behavior  || counter != 0 || irq_reload) && new_counter == 0 && irq_enable) begin
//        $write("MMC3 SCANLINE IRQ!\n");
        irq <= 1;
      end
      irq_reload <= 0;      
    end
    a12_ctr <= chr_ain[12] ? 4'b1111 : (a12_ctr != 0) ? a12_ctr - 4'b0001 : a12_ctr;
  end

  // The PRG bank to load. Each increment here is 8kb. So valid values are 0..63.
  reg [5:0] prgsel;
  always @* begin
    casez({prg_ain[14:13], prg_rom_bank_mode})
    3'b00_0: prgsel = prg_bank_0;  // $8000 mode 0
    3'b00_1: prgsel = 6'b111110;   // $8000 fixed to second last bank
    3'b01_?: prgsel = prg_bank_1;  // $A000 mode 0,1
    3'b10_0: prgsel = 6'b111110;   // $C000 fixed to second last bank
    3'b10_1: prgsel = prg_bank_0;  // $C000 mode 1
    3'b11_?: prgsel = 6'b111111;   // $E000 fixed to last bank
    endcase
    // mapper47 is limited to 128k PRG, the top bits are controlled by mapper47_multicart instead.
    if (mapper47) prgsel[5:4] = {1'b0, mapper47_multicart};
  end

  // The CHR bank to load. Each increment here is 1kb. So valid values are 0..255.
  reg [7:0] chrsel;
  always @* begin
    casez({chr_ain[12] ^ chr_a12_invert, chr_ain[11], chr_ain[10]})
    3'b00?: chrsel = {chr_bank_0, chr_ain[10]};
    3'b01?: chrsel = {chr_bank_1, chr_ain[10]};
    3'b100: chrsel = chr_bank_2;
    3'b101: chrsel = chr_bank_3;
    3'b110: chrsel = chr_bank_4;
    3'b111: chrsel = chr_bank_5;
    endcase
    // mapper47 is limited to 128k CHR, the top bit is controlled by mapper47_multicart instead.
    if (mapper47) chrsel[7] = mapper47_multicart;
  end

  wire [21:0] prg_aout_tmp = {3'b00_0,  prgsel, prg_ain[12:0]};

  assign {chr_allow, chr_aout} = 
      (TQROM && chrsel[6])   ? {1'b1,    9'b11_1111_111, chrsel[2:0], chr_ain[9:0]} :   // TQROM 8kb CHR-RAM
      (four_screen_mirroring && chr_ain[13]) ? {1'b1,    9'b11_1111_111, chr_ain[13], chr_ain[11:0]} :  // DxROM 8kb CHR-RAM
                             {flags[15], 4'b10_00, chrsel, chr_ain[9:0]};               // Standard MMC3

  assign prg_is_ram = prg_ain >= 'h6000 && prg_ain < 'h8000 && ram_enable && !(ram_protect && prg_write);
  assign prg_allow = prg_ain[15] && !prg_write || prg_is_ram && !mapper47;
  wire [21:0] prg_ram = {9'b11_1100_000, prg_ain[12:0]};
  assign prg_aout = prg_is_ram  && !mapper47 && !DxROM ? prg_ram : prg_aout_tmp;
  assign vram_a10 = !TxSROM ? (mirroring ? chr_ain[11] : chr_ain[10]) :	// TxSROM do not support mirroring
                                    chrsel[7];
  assign vram_ce = chr_ain[13] && !four_screen_mirroring;
endmodule

// MMC4 mapper chip. PRG ROM: 256kB. Bank Size: 16kB. CHR ROM: 128kB
module MMC4(input clk, input ce, input reset,
            input [31:0] flags,
            input [15:0] prg_ain, output [21:0] prg_aout,
            input prg_read, prg_write,                   // Read / write signals
            input [7:0] prg_din,
            output prg_allow,                            // Enable access to memory for the specified operation.
            input chr_read, input [13:0] chr_ain, output [21:0] chr_aout,
            output chr_allow,                      		// Allow write
            output vram_a10,                             // Value for A10 address line
            output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.

// PRG ROM bank select ($A000-$AFFF)
// 7  bit  0
// ---- ----
// xxxx PPPP
//      ||||
//      ++++- Select 16 KB PRG ROM bank for CPU $8000-$BFFF
  reg [3:0] prg_bank;

// CHR ROM $FD/0000 bank select ($B000-$BFFF)
// 7  bit  0
// ---- ----
// xxxC CCCC
//    | ||||
//    +-++++- Select 4 KB CHR ROM bank for PPU $0000-$0FFF
//            used when latch 0 = $FD
  reg   [4:0] chr_bank_0a;

// CHR ROM $FE/0000 bank select ($C000-$CFFF)
// 7  bit  0
// ---- ----
// xxxC CCCC
//    | ||||
//    +-++++- Select 4 KB CHR ROM bank for PPU $0000-$0FFF
//            used when latch 0 = $FE
   reg [4:0] chr_bank_0b;
   
// CHR ROM $FD/1000 bank select ($D000-$DFFF)
// 7  bit  0
// ---- ----
// xxxC CCCC
//    | ||||
//    +-++++- Select 4 KB CHR ROM bank for PPU $1000-$1FFF
//            used when latch 1 = $FD
  reg [4:0] chr_bank_1a;
   
// CHR ROM $FE/1000 bank select ($E000-$EFFF)
// 7  bit  0
// ---- ----
// xxxC CCCC
//    | ||||
//    +-++++- Select 4 KB CHR ROM bank for PPU $1000-$1FFF
//            used when latch 1 = $FE
  reg [4:0] chr_bank_1b; 
  
// Mirroring ($F000-$FFFF)
// 7  bit  0
// ---- ----
// xxxx xxxM
//         |
//         +- Select nametable mirroring (0: vertical; 1: horizontal)  
  reg mirroring;
  
  reg latch_0, latch_1;
  
  // Update registers
  always @(posedge clk) if (ce) begin
    if (reset)
	   prg_bank <= 4'b1110;	  
    else if (prg_write && prg_ain[15]) begin
      case(prg_ain[14:12])
      2: prg_bank <= prg_din[3:0];     // $A000
      3: chr_bank_0a <= prg_din[4:0];  // $B000
      4: chr_bank_0b <= prg_din[4:0];  // $C000
      5: chr_bank_1a <= prg_din[4:0];  // $D000
      6: chr_bank_1b <= prg_din[4:0];  // $E000
      7: mirroring <=  prg_din[0];     // $F000
      endcase
    end
  end
  
// PPU reads $0FD8 through $0FDF: latch 0 is set to $FD for subsequent reads
// PPU reads $0FE8 through $0FEF: latch 0 is set to $FE for subsequent reads
// PPU reads $1FD8 through $1FDF: latch 1 is set to $FD for subsequent reads
// PPU reads $1FE8 through $1FEF: latch 1 is set to $FE for subsequent reads
  always @(posedge clk) if (ce && chr_read) begin
    latch_0 <= (chr_ain & 14'h3ff8) == 14'h0fd8 ? 0 : (chr_ain & 14'h3ff8) == 14'h0fe8 ? 1 : latch_0;
    latch_1 <= (chr_ain & 14'h3ff8) == 14'h1fd8 ? 0 : (chr_ain & 14'h3ff8) == 14'h1fe8 ? 1 : latch_1;
  end
  
  // The PRG bank to load. Each increment here is 16kb. So valid values are 0..15.
  reg [3:0] prgsel;
  always @* begin
    casez(prg_ain[14])
    1'b0:    prgsel = prg_bank;
    default: prgsel = 4'b1111;
    endcase
  end
  wire [21:0] prg_aout_tmp = {4'b00_00, prgsel, prg_ain[13:0]};

  // The CHR bank to load. Each increment here is 4kb. So valid values are 0..31.
  reg [4:0] chrsel;
  always @* begin
    casez({chr_ain[12], latch_0, latch_1})
    3'b00?: chrsel = chr_bank_0a;
    3'b01?: chrsel = chr_bank_0b;
    3'b1?0: chrsel = chr_bank_1a;
    3'b1?1: chrsel = chr_bank_1b;
    endcase
  end
  assign chr_aout = {5'b100_00, chrsel, chr_ain[11:0]};
  
  // The a10 VRAM address line. (Used for mirroring)
  assign vram_a10 = mirroring ? chr_ain[11] : chr_ain[10];
  assign vram_ce = chr_ain[13];
  
  assign chr_allow = flags[15];
  
  wire prg_is_ram = prg_ain >= 'h6000 && prg_ain < 'h8000;
  assign prg_allow = prg_ain[15] && !prg_write ||
                     prg_is_ram;
  wire [21:0] prg_ram = {9'b11_1100_000, prg_ain[12:0]};
  assign prg_aout = prg_is_ram ? prg_ram : prg_aout_tmp;

endmodule

module MMC5(input clk, input ce, input reset,
            input [31:0] flags,
            input [19:0] ppuflags,
            input [15:0] prg_ain, output [21:0] prg_aout,
            input prg_read, prg_write,                   // Read / write signals
            input [7:0] prg_din, output reg [7:0] prg_dout,
            output prg_allow,                            // Enable access to memory for the specified operation.
            input [13:0] chr_ain, output reg [21:0] chr_aout,
            output reg [7:0] chr_dout, output has_chr_dout,
            output chr_allow,                            // Allow write
            output vram_a10,                             // Value for A10 address line
            output vram_ce,                              // True if the address should be routed to the internal 2kB VRAM.
            output irq);
  reg [1:0] prg_mode, chr_mode;
  reg prg_protect_1, prg_protect_2;
  reg [1:0] extended_ram_mode;
  reg [7:0] mirroring;
  reg [7:0] fill_tile;
  reg [1:0] fill_attr;
  reg [2:0] prg_ram_bank;
  reg [7:0] prg_bank_0, prg_bank_1, prg_bank_2;
  reg [6:0] prg_bank_3;
  reg [9:0] chr_bank_0, chr_bank_1, chr_bank_2, chr_bank_3,
            chr_bank_4, chr_bank_5, chr_bank_6, chr_bank_7,
            chr_bank_8, chr_bank_9, chr_bank_a, chr_bank_b;
  reg [1:0] upper_chr_bank_bits;
  reg chr_last; // Which CHR set was written to last?
  
  reg [4:0] vsplit_startstop;
  reg vsplit_enable, vsplit_side;
  reg [7:0] vsplit_scroll, vsplit_bank;
  
  reg [7:0] irq_scanline;
  reg irq_enable;
  reg irq_pending;
  
  reg [7:0] multiplier_1;
  reg [7:0] multiplier_2; 
  wire [15:0] multiply_result = multiplier_1 * multiplier_2;
  
  reg [7:0] expansion_ram[0:1023]; // Block RAM, otherwise we need to time multiplex..
  reg [7:0] last_read_ram;
  
  // unpack ppu flags
  wire ppu_in_frame = ppuflags[0];
  wire ppu_sprite16 = ppuflags[1];
  wire [8:0] ppu_cycle = ppuflags[10:2]; 
  wire [8:0] ppu_scanline = ppuflags[19:11];
  
  // Handle IO register writes  
  always @(posedge clk) begin
    if (ce) begin
      if (prg_write && prg_ain[15:10] == 6'b010100) begin // $5000-$53FF
        if (prg_ain <= 16'h5113)
          $write("%X <= %X (%d)\n", prg_ain, prg_din, ppu_scanline);
        casez(prg_ain[9:0])
        10'h100: prg_mode <= prg_din[1:0];
        10'h101: chr_mode <= prg_din[1:0];
        10'h102: prg_protect_1 <= (prg_din[1:0] == 2'b10);
        10'h103: prg_protect_2 <= (prg_din[1:0] == 2'b01);
        10'h104: extended_ram_mode <= prg_din[1:0];
        10'h105: mirroring <= prg_din;
        10'h106: fill_tile <= prg_din;
        10'h107: fill_attr <= prg_din[1:0];
        10'h113: prg_ram_bank <= prg_din[2:0];
        10'h114: prg_bank_0 <= prg_din;
        10'h115: prg_bank_1 <= prg_din;
        10'h116: prg_bank_2 <= prg_din;
        10'h117: prg_bank_3 <= prg_din[6:0];
        10'h120: chr_bank_0 <= {upper_chr_bank_bits, prg_din};
        10'h121: chr_bank_1 <= {upper_chr_bank_bits, prg_din};
        10'h122: chr_bank_2 <= {upper_chr_bank_bits, prg_din};
        10'h123: chr_bank_3 <= {upper_chr_bank_bits, prg_din};
        10'h124: chr_bank_4 <= {upper_chr_bank_bits, prg_din};
        10'h125: chr_bank_5 <= {upper_chr_bank_bits, prg_din};
        10'h126: chr_bank_6 <= {upper_chr_bank_bits, prg_din};
        10'h127: chr_bank_7 <= {upper_chr_bank_bits, prg_din};
        10'h128: chr_bank_8  <= {upper_chr_bank_bits, prg_din};
        10'h129: chr_bank_9  <= {upper_chr_bank_bits, prg_din};
        10'h12a: chr_bank_a  <= {upper_chr_bank_bits, prg_din};
        10'h12b: chr_bank_b  <= {upper_chr_bank_bits, prg_din};
        10'h130: upper_chr_bank_bits <= prg_din[1:0];
        10'h200: {vsplit_enable, vsplit_side, vsplit_startstop} = {prg_din[7:6], prg_din[4:0]};
        10'h201: vsplit_scroll <= prg_din;
        10'h202: vsplit_bank <= prg_din;
        10'h203: irq_scanline <= prg_din;
        10'h204: irq_enable <= prg_din[7];
        10'h205: multiplier_1 <= prg_din;
        10'h206: multiplier_2 <= prg_din;
        default: begin end
        endcase
        
        // Remember which set of CHR was written to last.
        if (prg_ain[9:0] >= 10'h120 && prg_ain[9:0] < 10'h130)
          chr_last <= prg_ain[3];
      end
      
      // Mode 0/1 - Not readable (returns open bus), can only be written while the PPU is rendering (otherwise, 0 is written)
      // Mode 2 - Readable and writable
      // Mode 3 - Read-only
      if (prg_write && prg_ain[15:10] == 6'b010111) begin // $5C00-$5FFF
        if (extended_ram_mode != 3)
          expansion_ram[prg_ain[9:0]] <= (extended_ram_mode[1] || ppu_in_frame) ? prg_din : 0;
      end
    end
    if (reset) begin
      prg_bank_3 <= 7'h7F;
      prg_mode <= 3;
    end
  end
  
  // Read from MMC5
  always @* begin
    prg_dout = 8'hFF; // By default open bus.
    if (prg_ain[15:10] == 6'b010111 && extended_ram_mode[1]) begin
      prg_dout = last_read_ram;
    end else if (prg_ain == 16'h5204) begin
      prg_dout = {irq_pending, ppu_in_frame, 6'b111111};
    end else if (prg_ain == 16'h5205) begin
      prg_dout = multiply_result[7:0];
    end else if (prg_ain == 16'h5206) begin
      prg_dout = multiply_result[15:8];
    end
  end
  
  // Determine IRQ handling
  reg last_scanline, irq_trig;
  always @(posedge clk) if (ce) begin
    if (prg_read && prg_ain == 16'h5204)
      irq_pending <= 0;
    irq_trig <= (irq_scanline != 0 && irq_scanline < 240 && ppu_scanline == {1'b0, irq_scanline});
    last_scanline <= ppu_scanline[0];
    if (ppu_scanline[0] != last_scanline && irq_trig)
      irq_pending <= 1;
  end
  assign irq = irq_pending && irq_enable;

  // Determine if vertical split is active.
  reg [5:0] cur_tile;     // Current tile the PPU is fetching
  reg [5:0] new_cur_tile; // New value for |cur_tile|
  reg [7:0] vscroll;      // Current y scroll for the split region
  reg last_in_split_area, in_split_area;

  // Compute if we're in the split area right now by counting PPU tiles.
  always @* begin
    new_cur_tile = (ppu_cycle[8:3] == 40) ? 0 : (cur_tile + 6'b1);
    in_split_area = last_in_split_area;
    if (ppu_cycle[2:0] == 0 && ppu_cycle < 336) begin
      if (new_cur_tile == 0)
        in_split_area = !vsplit_side;
      else if (new_cur_tile == {1'b0, vsplit_startstop})
        in_split_area = vsplit_side;
      else if (new_cur_tile == 34)
        in_split_area = 0;
    end
  end
  always @(posedge clk) if (ce) begin
    last_in_split_area <= in_split_area;
    if (ppu_cycle[2:0] == 0 && ppu_cycle < 336)
      cur_tile <= new_cur_tile;
  end
  // Keep track of scroll
  always @(posedge clk) if (ce) begin
    if (ppu_cycle == 319)
      vscroll <= ppu_scanline[8] ? vsplit_scroll : 
                 (vscroll == 239) ? 8'b0 : vscroll + 8'b1;
  end

  // Mirroring bits
  // %00 = NES internal NTA
  // %01 = NES internal NTB
  // %10 = use ExRAM as NT
  // %11 = Fill Mode
  wire [1:0] mirrbits = (chr_ain[11:10] == 0) ? mirroring[1:0] : 
                        (chr_ain[11:10] == 1) ? mirroring[3:2] : 
                        (chr_ain[11:10] == 2) ? mirroring[5:4] : 
                                                mirroring[7:6];

  // Compute the new overriden nametable/attr address the split will read from instead
  // when the VSplit is active.
  // Cycle 0, 1 = nametable
  // Cycle 2, 3 = attribute
  // Named it loopy so I can copypaste from PPU code :)
  wire [9:0] loopy = {vscroll[7:3], cur_tile[4:0]};              
  wire [9:0] split_addr = (ppu_cycle[1] == 0) ? loopy :                            // name table
                                                {4'b1111, loopy[9:7], loopy[4:2]}; // attribute table
  // Selects 2 out of the attr bits read from exram.
  wire [1:0] split_attr = (!loopy[1] && !loopy[6]) ? last_read_ram[1:0] : 
                          ( loopy[1] && !loopy[6]) ? last_read_ram[3:2] :
                          (!loopy[1] &&  loopy[6]) ? last_read_ram[5:4] : 
                                                     last_read_ram[7:6];
  // If splitting is active or not
  wire insplit = in_split_area && vsplit_enable;

  // Currently reading the attribute byte?
  wire exattr_read = (extended_ram_mode == 1) && ppu_cycle[1];
  
  // If the current chr read should be redirected from |chr_dout| instead.
  assign has_chr_dout = chr_ain[13] && (mirrbits[1] || insplit || exattr_read);
  wire [1:0] override_attr = insplit ? split_attr : (extended_ram_mode == 1) ? last_read_ram[7:6] : fill_attr;
  always @* begin
    if (ppu_cycle[1] == 0) begin
      // Name table fetch
      if (insplit || mirrbits[0] == 0) chr_dout = (extended_ram_mode[1] ? 8'b0 : last_read_ram);
      else begin
        $write("Inserting filltile!\n");
        chr_dout = fill_tile;
      end
    end else begin
      // Attribute table fetch
      if (!insplit && !exattr_read && mirrbits[0] == 0) chr_dout = (extended_ram_mode[1] ? 8'b0 : last_read_ram);
      else chr_dout = {override_attr, override_attr, override_attr, override_attr};
    end
  end

  // Handle reading from the expansion ram.
  // 0 - Use as extra nametable (possibly for split mode)
  // 1 - Use as extended attribute data OR an extra nametable
  // 2 - Use as ordinary RAM
  // 3 - Use as ordinary RAM, write protected
  wire [9:0] exram_read_addr = extended_ram_mode[1] ? prg_ain[9:0] : 
                               insplit              ? split_addr :
                                                      chr_ain[9:0];
  always @(posedge clk)
    last_read_ram <= expansion_ram[exram_read_addr];

  // Compute PRG address to read from.
  reg [7:0] prgsel;
  always @* begin
    casez({prg_mode, prg_ain[15:13]})
    5'b??_0??: prgsel = {5'b1xxxx, prg_ram_bank};                // $6000-$7FFF all modes
    5'b00_1??: prgsel = {1'b1, prg_bank_3[6:2], prg_ain[14:13]}; // $8000-$FFFF mode 0, 32kB (prg_bank_3, skip 2 bits)

    5'b01_10?: prgsel = {      prg_bank_1[7:1], prg_ain[13]};    // $8000-$BFFF mode 1, 16kB (prg_bank_1, skip 1 bit)
    5'b01_11?: prgsel = {1'b1, prg_bank_3[6:1], prg_ain[13]};    // $C000-$FFFF mode 1, 16kB (prg_bank_3, skip 1 bit)

    5'b10_10?: prgsel = {      prg_bank_1[7:1], prg_ain[13]};    // $8000-$BFFF mode 2, 16kB (prg_bank_1, skip 1 bit)
    5'b10_110: prgsel = {      prg_bank_2};                      // $C000-$DFFF mode 2, 8kB  (prg_bank_2)
    5'b10_111: prgsel = {1'b1, prg_bank_3};                      // $E000-$FFFF mode 2, 8kB  (prg_bank_3)

    5'b11_100: prgsel = {      prg_bank_0};                      // $8000-$9FFF mode 3, 8kB (prg_bank_0)
    5'b11_101: prgsel = {      prg_bank_1};                      // $A000-$BFFF mode 3, 8kB (prg_bank_1)
    5'b11_110: prgsel = {      prg_bank_2};                      // $C000-$DFFF mode 3, 8kB (prg_bank_2)
    5'b11_111: prgsel = {1'b1, prg_bank_3};                      // $E000-$FFFF mode 3, 8kB (prg_bank_3)
    endcase
    prgsel[7] = !prgsel[7]; // 0 means RAM, doh.
    
    // Limit to 64k RAM.
    if (prgsel[7])
      prgsel[6:3] = 0;
  end
  assign prg_aout = {1'b0, prgsel, prg_ain[12:0]};    // 8kB banks

  // Registers $5120-$5127 apply to sprite graphics and $5128-$512B for background graphics, but ONLY when 8x16 sprites are enabled.
  // Otherwise, the last set of registers written to (either $5120-$5127 or $5128-$512B) will be used for all graphics.
  // 0 if using $5120-$5127, 1 if using $5128-$512F
  wire is_bg_fetch = !(ppu_cycle[8] && !ppu_cycle[6]);
  wire chrset = ppu_sprite16 ? is_bg_fetch : chr_last; 
  reg [9:0] chrsel;
  always @* begin
    casez({chr_mode, chr_ain[12:10], chrset})
    6'b00_???_0: chrsel = {chr_bank_7[6:0], chr_ain[12:10]}; // $0000-$1FFF mode 0, 8 kB
    6'b00_???_1: chrsel = {chr_bank_b[6:0], chr_ain[12:10]}; // $0000-$1FFF mode 0, 8 kB
    
    6'b01_0??_0: chrsel = {chr_bank_3[7:0], chr_ain[11:10]}; // $0000-$0FFF mode 1, 4 kB
    6'b01_1??_0: chrsel = {chr_bank_7[7:0], chr_ain[11:10]}; // $1000-$1FFF mode 1, 4 kB
    6'b01_???_1: chrsel = {chr_bank_b[7:0], chr_ain[11:10]}; // $0000-$0FFF mode 1, 4 kB

    6'b10_00?_0: chrsel = {chr_bank_1[8:0], chr_ain[10]};    // $0000-$07FF mode 2, 2 kB
    6'b10_01?_0: chrsel = {chr_bank_3[8:0], chr_ain[10]};    // $0800-$0FFF mode 2, 2 kB
    6'b10_10?_0: chrsel = {chr_bank_5[8:0], chr_ain[10]};    // $1000-$17FF mode 2, 2 kB
    6'b10_11?_0: chrsel = {chr_bank_7[8:0], chr_ain[10]};    // $1800-$1FFF mode 2, 2 kB
    6'b10_?0?_1: chrsel = {chr_bank_9[8:0], chr_ain[10]};    // $0000-$07FF mode 2, 2 kB
    6'b10_?1?_1: chrsel = {chr_bank_b[8:0], chr_ain[10]};    // $0800-$0FFF mode 2, 2 kB

    6'b11_000_0: chrsel = chr_bank_0;                        // $0000-$03FF mode 3, 1 kB
    6'b11_001_0: chrsel = chr_bank_1;                        // $0400-$07FF mode 3, 1 kB
    6'b11_010_0: chrsel = chr_bank_2;                        // $0800-$0BFF mode 3, 1 kB
    6'b11_011_0: chrsel = chr_bank_3;                        // $0C00-$0FFF mode 3, 1 kB
    6'b11_100_0: chrsel = chr_bank_4;                        // $1000-$13FF mode 3, 1 kB
    6'b11_101_0: chrsel = chr_bank_5;                        // $1400-$17FF mode 3, 1 kB
    6'b11_110_0: chrsel = chr_bank_6;                        // $1800-$1BFF mode 3, 1 kB
    6'b11_111_0: chrsel = chr_bank_7;                        // $1C00-$1FFF mode 3, 1 kB
    6'b11_?00_1: chrsel = chr_bank_8;                        // $0000-$03FF mode 3, 1 kB
    6'b11_?01_1: chrsel = chr_bank_9;                        // $0400-$07FF mode 3, 1 kB
    6'b11_?10_1: chrsel = chr_bank_a;                        // $0800-$0BFF mode 3, 1 kB
    6'b11_?11_1: chrsel = chr_bank_b;                        // $0C00-$0FFF mode 3, 1 kB
    endcase
  
    chr_aout = {2'b10, chrsel, chr_ain[9:0]};    // 1kB banks
    
    // Override |chr_aout| if we're in a vertical split.
    if (insplit) begin
      $write("In vertical split!\n");
      chr_aout = {2'b10, vsplit_bank, chr_ain[11:3], vscroll[2:0]};
    end else if (extended_ram_mode == 1 && is_bg_fetch) begin
      $write("In exram thingy!\n");
      // Extended attribute mode. Replace the page with the page from exram.
      chr_aout = {2'b10, upper_chr_bank_bits, last_read_ram[5:0], chr_ain[11:0]};
    end
      
  end
  
  // The a10 VRAM address line. (Used for mirroring)
  assign vram_a10 = mirrbits[0];
  assign vram_ce = chr_ain[13] && !mirrbits[1];
  
  // Writing to RAM is enabled only when the protect bits say so.  
  wire prg_ram_we = prg_protect_1 && prg_protect_2;
  assign prg_allow = (prg_ain >= 16'h6000) && (!prg_write || prgsel[7] && prg_ram_we);
  
  // MMC5 boards typically have no CHR RAM.
  assign chr_allow = flags[15];
endmodule

// iNES mapper 64 and 158 - Tengen's version of MMC3
module Rambo1(input clk, input ce, input reset,
              input [31:0] flags,
              input [15:0] prg_ain, output [21:0] prg_aout,
              input prg_read, prg_write,                   // Read / write signals
              input [7:0] prg_din,
              output prg_allow,                            // Enable access to memory for the specified operation.
              input [13:0] chr_ain, output [21:0] chr_aout,
              output chr_allow,                            // Allow write
              output vram_a10,                             // Value for A10 address line
              output vram_ce,                              // True if the address should be routed to the internal 2kB VRAM.
              output reg irq);
  reg [3:0] bank_select;             // Register to write to next
  reg prg_rom_bank_mode;             // Mode for PRG banking
  reg chr_K;                         // Mode for CHR banking
  reg chr_a12_invert;                // Mode for CHR banking
  reg mirroring;                     // 0 = vertical, 1 = horizontal
  reg irq_enable, irq_reload;        // IRQ enabled, and IRQ reload requested
  reg [7:0] irq_latch, counter;      // IRQ latch value and current counter
  reg want_irq;
  reg [7:0] chr_bank_0, chr_bank_1;  // Selected CHR banks
  reg [7:0] chr_bank_2, chr_bank_3, chr_bank_4, chr_bank_5;
  reg [7:0] chr_bank_8, chr_bank_9;
  reg [5:0] prg_bank_0, prg_bank_1, prg_bank_2;  // Selected PRG banks
  reg irq_cycle_mode;
  reg [1:0] cycle_counter;
 
  // Mapper has vram_a10 wired to CHR A17
  wire mapper64 = (flags[7:0] == 64);

  reg is_interrupt;  // Not a reg!
  
  // This code detects rising edges on a12.
  reg old_a12_edge;
  reg [1:0] a12_ctr;
  wire a12_edge = (chr_ain[12] && a12_ctr == 0) || old_a12_edge;
  always @(posedge clk) begin
    old_a12_edge <= a12_edge && !ce;
    a12_ctr <= chr_ain[12] ? 2'b11 : (a12_ctr != 0 && ce) ? a12_ctr - 2'b01 : a12_ctr;
  end
  
  always @(posedge clk) if (reset) begin
    bank_select <= 0;
    prg_rom_bank_mode <= 0;
    chr_K <= 0;
    chr_a12_invert <= 0;
    mirroring <= 0;
    {irq_enable, irq_reload} <= 0;
    {irq_latch, counter} <= 0;
    want_irq <= 0;
    {chr_bank_0, chr_bank_1} <= 0;
    {chr_bank_2, chr_bank_3, chr_bank_4, chr_bank_5} <= 0;
    {chr_bank_8, chr_bank_9} <= 0;
    {prg_bank_0, prg_bank_1, prg_bank_2} <= 6'b111111;
    irq_cycle_mode <= 0;
    cycle_counter <= 0;
    irq <= 0;
  end else if (ce) begin
    cycle_counter <= cycle_counter + 1;
        
    if (prg_write && prg_ain[15]) begin
      case({prg_ain[14:13], prg_ain[0]})
      // Bank select ($8000-$9FFE, even)
      3'b00_0: {chr_a12_invert, prg_rom_bank_mode, chr_K, bank_select} <= {prg_din[7:5], prg_din[3:0]}; 
      // Bank data ($8001-$9FFF, odd)
      3'b00_1:
        case (bank_select) 
        0: chr_bank_0 <= prg_din;       // Select 2 (K=0) or 1 (K=1) KB CHR bank at PPU $0000 (or $1000);
        1: chr_bank_1 <= prg_din;       // Select 2 (K=0) or 1 (K=1) KB CHR bank at PPU $0800 (or $1800);
        2: chr_bank_2 <= prg_din;       // Select 1 KB CHR bank at PPU $1000-$13FF (or $0000-$03FF);
        3: chr_bank_3 <= prg_din;       // Select 1 KB CHR bank at PPU $1400-$17FF (or $0400-$07FF);
        4: chr_bank_4 <= prg_din;       // Select 1 KB CHR bank at PPU $1800-$1BFF (or $0800-$0BFF);
        5: chr_bank_5 <= prg_din;       // Select 1 KB CHR bank at PPU $1C00-$1FFF (or $0C00-$0FFF);
        6: prg_bank_0 <= prg_din[5:0];  // Select 8 KB PRG ROM bank at $8000-$9FFF (or $C000-$DFFF);
        7: prg_bank_1 <= prg_din[5:0];  // Select 8 KB PRG ROM bank at $A000-$BFFF
        8: chr_bank_8 <= prg_din;       // If K=1, Select 1 KB CHR bank at PPU $0400 (or $1400);
        9: chr_bank_9 <= prg_din;       // If K=1, Select 1 KB CHR bank at PPU $0C00 (or $1C00)
        15: prg_bank_2 <= prg_din[5:0]; // Select 8 KB PRG ROM bank at $C000-$DFFF (or $8000-$9FFF);
        endcase
      3'b01_0: mirroring <= prg_din[0];                   // Mirroring ($A000-$BFFE, even)
      3'b01_1: begin end
      3'b10_0: irq_latch <= prg_din;                      // IRQ latch ($C000-$DFFE, even)
      3'b10_1: begin 
                 {irq_reload, irq_cycle_mode} <= {1'b1, prg_din[0]}; // IRQ reload ($C001-$DFFF, odd)
                 cycle_counter <= 0;
               end
      3'b11_0: {irq_enable, irq} <= 2'b0;                 // IRQ disable ($E000-$FFFE, even)
      3'b11_1: irq_enable <= 1;                           // IRQ enable ($E001-$FFFF, odd)
      endcase
    end
    is_interrupt = irq_cycle_mode ? (cycle_counter == 3) : a12_edge;
    if (is_interrupt) begin
      if (irq_reload || counter == 0) begin
        counter <= irq_latch;
        want_irq <= irq_reload;
      end else begin
        counter <= counter - 1;
        want_irq <= 1;
      end
      if (counter == 0 && want_irq && !irq_reload && irq_enable)
        irq <= 1;
      irq_reload <= 0;
    end
    
  end
  // The PRG bank to load. Each increment here is 8kb. So valid values are 0..63.
  reg [5:0] prgsel;
  always @* begin
    casez({prg_ain[14:13], prg_rom_bank_mode})
    3'b00_0: prgsel = prg_bank_0;  // $8000 is R:6
    3'b01_0: prgsel = prg_bank_1;  // $A000 is R:7
    3'b10_0: prgsel = prg_bank_2;  // $C000 is R:F
    3'b11_0: prgsel = 6'b111111;   // $E000 fixed to last bank
    3'b00_1: prgsel = prg_bank_2;  // $8000 is R:F
    3'b01_1: prgsel = prg_bank_0;  // $A000 is R:6
    3'b10_1: prgsel = prg_bank_1;  // $C000 is R:7
    3'b11_1: prgsel = 6'b111111;   // $E000 fixed to last bank
    endcase
  end
  // The CHR bank to load. Each increment here is 1kb. So valid values are 0..255.
  reg [7:0] chrsel;
  always @* begin
    casez({chr_ain[12] ^ chr_a12_invert, chr_ain[11], chr_ain[10], chr_K})
    4'b00?_0: chrsel = {chr_bank_0[7:1], chr_ain[10]};
    4'b01?_0: chrsel = {chr_bank_1[7:1], chr_ain[10]};
    4'b000_1: chrsel = chr_bank_0;
    4'b001_1: chrsel = chr_bank_8;
    4'b010_1: chrsel = chr_bank_1;
    4'b011_1: chrsel = chr_bank_9;
    4'b100_?: chrsel = chr_bank_2;
    4'b101_?: chrsel = chr_bank_3;
    4'b110_?: chrsel = chr_bank_4;
    4'b111_?: chrsel = chr_bank_5;
    endcase
  end
  assign prg_aout = {3'b00_0,  prgsel, prg_ain[12:0]};
  assign {chr_allow, chr_aout} = {flags[15], 4'b10_00, chrsel, chr_ain[9:0]};
  assign prg_allow = prg_ain[15] && !prg_write;
  assign vram_a10 = mapper64 ? chrsel[7] :  // Mapper 64 controls mirroring by switching the top bits of the CHR address
                    mirroring ? chr_ain[11] : chr_ain[10];
  assign vram_ce = chr_ain[13];
endmodule


// #13 - CPROM - Used by Videomation
module Mapper13(input clk, input ce, input reset,
                input [31:0] flags,
                input [15:0] prg_ain, output [21:0] prg_aout,
                input prg_read, prg_write,                   // Read / write signals
                input [7:0] prg_din,
                output prg_allow,                            // Enable access to memory for the specified operation.
                input [13:0] chr_ain, output [21:0] chr_aout,
                output chr_allow,                      // Allow write
                output vram_a10,                             // Value for A10 address line
                output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.
  reg [1:0] chr_bank;
  always @(posedge clk) if (reset) begin
    chr_bank <= 0;
  end else if (ce) begin
    if (prg_ain[15] && prg_write)
      chr_bank <= prg_din[1:0];
  end
  assign prg_aout = {7'b00_0000_0, prg_ain[14:0]};
  assign prg_allow = prg_ain[15] && !prg_write;
  assign chr_allow = flags[15];
  assign chr_aout = {8'b01_0000_00, chr_ain[12] ? chr_bank : 2'b00, chr_ain[11:0]};
  assign vram_ce = chr_ain[13];
  assign vram_a10 = flags[14] ? chr_ain[10] : chr_ain[11];
endmodule

// #15 -  100-in-1 Contra Function 16
module Mapper15(input clk, input ce, input reset,
                input [31:0] flags,
                input [15:0] prg_ain, output [21:0] prg_aout,
                input prg_read, prg_write,                   // Read / write signals
                input [7:0] prg_din,
                output prg_allow,                            // Enable access to memory for the specified operation.
                input [13:0] chr_ain, output [21:0] chr_aout,
                output chr_allow,                      // Allow write
                output vram_a10,                             // Value for A10 address line
                output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.
// 15 bit  8 7  bit  0  Address bus
// ---- ---- ---- ----
// 1xxx xxxx xxxx xxSS
// |                ||
// |                ++- Select PRG ROM bank mode
// |                    0: 32K; 1: 128K (UNROM style); 2: 8K; 3: 16K
// +------------------- Always 1
// 7  bit  0  Data bus
// ---- ----
// bMBB BBBB
// |||| ||||
// ||++-++++- Select 16 KB PRG ROM bank
// |+-------- Select nametable mirroring mode (0=vertical; 1=horizontal)
// +--------- Select 8 KB half of 16 KB PRG ROM bank
//            (should be 0 except in bank mode 0)
  reg [1:0] prg_rom_bank_mode;
  reg prg_rom_bank_lowbit;
  reg mirroring;
  reg [5:0] prg_rom_bank;
  always @(posedge clk) if (reset) begin
    prg_rom_bank_mode <= 0;
    prg_rom_bank_lowbit <= 0;
    mirroring <= 0;
    prg_rom_bank <= 0;
  end else if (ce) begin
    if (prg_ain[15] && prg_write)
      {prg_rom_bank_mode, prg_rom_bank_lowbit, mirroring, prg_rom_bank} <= {prg_ain[1:0], prg_din[7:0]};
  end
  reg [6:0] prg_bank;
  always begin
    casez({prg_rom_bank_mode, prg_ain[14]})
    // Bank mode 0 ( 32K ) / CPU $8000-$BFFF: Bank B / CPU $C000-$FFFF: Bank (B OR 1)
    3'b00_0: prg_bank = {prg_rom_bank, prg_ain[13]};
    3'b00_1: prg_bank = {prg_rom_bank | 6'b1, prg_ain[13]};
    // Bank mode 1 ( 128K ) / CPU $8000-$BFFF: Switchable 16 KB bank B / CPU $C000-$FFFF: Fixed to last bank in the cart
    3'b01_0: prg_bank = {prg_rom_bank, prg_ain[13]};
    3'b01_1: prg_bank = {6'b111111, prg_ain[13]};
    // Bank mode 2 ( 8K ) / CPU $8000-$9FFF: Sub-bank b of 16 KB PRG ROM bank B / CPU $A000-$FFFF: Mirrors of $8000-$9FFF
    3'b10_?: prg_bank = {prg_rom_bank, prg_rom_bank_lowbit};
    // Bank mode 3 ( 16K ) / CPU $8000-$BFFF: 16 KB bank B / CPU $C000-$FFFF: Mirror of $8000-$BFFF
    3'b11_?: prg_bank = {prg_rom_bank, prg_ain[13]};
    endcase
  end
  assign prg_aout = {2'b00, prg_bank, prg_ain[12:0]};
  assign prg_allow = prg_ain[15] && !prg_write;
  assign chr_allow = flags[15]; // CHR RAM?
  assign chr_aout = {9'b10_0000_000, chr_ain[12:0]};
  assign vram_ce = chr_ain[13];
  assign vram_a10 = mirroring ? chr_ain[11] : chr_ain[10];
endmodule

// Mapper 16, Bandai
module Mapper16(input clk, input ce, input reset,
            input [31:0] flags,
            input [15:0] prg_ain, output [21:0] prg_aout,
            input prg_read, prg_write,                   // Read / write signals
            input [7:0] prg_din, output [7:0] prg_dout,
            output prg_allow,                            // Enable access to memory for the specified operation.
            input [13:0] chr_ain, output [21:0] chr_aout,
            output chr_allow,                      		// Allow write
            output reg vram_a10,                         // Value for A10 address line
            output vram_ce,                     			// True if the address should be routed to the internal 2kB VRAM.
				output reg irq); 

	reg [3:0] prg_bank;
	reg [7:0] chr_bank_0, chr_bank_1, chr_bank_2, chr_bank_3,
				 chr_bank_4, chr_bank_5, chr_bank_6, chr_bank_7;
	reg [3:0] prg_sel;
	reg [1:0] mirroring;
	reg irq_enable;
	reg [15:0] irq_counter;
	
	always @(posedge clk) if (reset) begin
		prg_bank <= 4'hF;
		chr_bank_0 <= 0;
		chr_bank_1 <= 0;
		chr_bank_2 <= 0;
		chr_bank_3 <= 0;
		chr_bank_4 <= 0;
		chr_bank_5 <= 0;
		chr_bank_6 <= 0;
		chr_bank_7 <= 0;
		mirroring <= 0;
		irq_counter <= 0;
	end else if (ce) begin
		if (prg_write)
			if(prg_ain >= 'h6000)				// Cover all from $6000 to $FFFF to maximize compatibility
				case(prg_ain & 'hf)				// Registers are mapped every 16 bytes
				'h0: chr_bank_0 <= prg_din[7:0];
				'h1: chr_bank_1 <= prg_din[7:0];
				'h2: chr_bank_2 <= prg_din[7:0];
				'h3: chr_bank_3 <= prg_din[7:0];
				'h4: chr_bank_4 <= prg_din[7:0];
				'h5: chr_bank_5 <= prg_din[7:0];
				'h6: chr_bank_6 <= prg_din[7:0];
				'h7: chr_bank_7 <= prg_din[7:0];
				'h8: prg_bank <= prg_din[3:0];
				'h9: mirroring <= prg_din[1:0];
				'ha: irq_enable <= prg_din[0];
				'hb: irq_counter[7:0] <= prg_din[7:0];
				'hc: irq_counter[15:8] <= prg_din[7:0];
//				'hd: RAM enable or EEPROM control
				endcase

		if (irq_enable)
			irq_counter <= irq_counter - 16'd1;
		else begin
			irq <= 1'b0;	// IRQ ACK
		end	
		
		if (irq_counter == 16'h0000)
			irq <= 1'b1;	// IRQ
			
	end
	
	always begin
      // mirroring
      casez(mirroring[1:0])
      2'b00:   vram_a10 = {chr_ain[10]};    // vertical
      2'b01:   vram_a10 = {chr_ain[11]};    // horizontal
      2'b1?:   vram_a10 = {mirroring[0]};   // single screen lower
      endcase
	end 
	
   reg [3:0] prgsel;  
	always begin
		case(prg_ain[15:14])
		2'b10: 	prgsel = prg_bank;			// $8000 is swapable
		2'b11: 	prgsel = 4'hF;					// $C000 is hardwired to last bank
		endcase
	end
	
   reg [7:0] chrsel;  
   always begin
    casez(chr_ain[12:10])
    0: chrsel = chr_bank_0;
    1: chrsel = chr_bank_1;
    2: chrsel = chr_bank_2;
    3: chrsel = chr_bank_3;
    4: chrsel = chr_bank_4;
    5: chrsel = chr_bank_5;
    6: chrsel = chr_bank_6;
    7: chrsel = chr_bank_7;
    endcase
   end	
	assign chr_aout = {4'b10_00, chrsel, chr_ain[9:0]};					// 1kB banks
	wire [21:0] prg_aout_tmp = {4'b00_00, prgsel, prg_ain[13:0]};  	// 16kB banks	
	
	wire prg_is_ram = (prg_ain >= 'h6000) && (prg_ain < 'h8000);
   wire [21:0] prg_ram = {9'b11_1100_000, prg_ain[12:0]};
   assign prg_aout = prg_is_ram ? prg_ram : prg_aout_tmp;
	assign prg_dout = prg_is_ram ? 8'h00 : 8'hFF;							// EEPROM stub
  
   assign prg_allow = prg_ain[15] && !prg_write ||
                     prg_is_ram;
	assign chr_allow = flags[15];
	assign vram_ce = chr_ain[13];
endmodule

// Tepples/Multi-discrete mapper
// This mapper can emulate other mappers,  such as mapper #0, mapper #2
module Mapper28(input clk, input ce, input reset,
                input [31:0] flags,
                input [15:0] prg_ain, output [21:0] prg_aout,
                input prg_read, prg_write,                   // Read / write signals
                input [7:0] prg_din,
                output prg_allow,                            // Enable access to memory for the specified operation.
                input [13:0] chr_ain, output [21:0] chr_aout,
                output chr_allow,                      // Allow write
                output reg vram_a10,                         // Value for A10 address line
                output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.
    reg [6:0] a53prg;    // output PRG ROM (A14-A20 on ROM)
    reg [1:0] a53chr;    // output CHR RAM (A13-A14 on RAM)
   
    reg [3:0] inner;    // "inner" bank at 01h
    reg [5:0] mode;     // mode register at 80h
    reg [5:0] outer;    // "outer" bank at 81h  
    reg [1:0] selreg;   // selector register
    
    // Allow writes to 0x5000 only when launching through the proper mapper ID.
    wire [7:0] mapper = flags[7:0];
    wire allow_select = (mapper == 8'd28); 

    always @(posedge clk) if (reset) begin
      mode[5:2] <= 0;         // NROM mode, 32K mode
      outer[5:0] <= 6'h3f;    // last bank
      inner <= 0;
      selreg <= 1;
      
      // Set value for mirroring
      if (mapper == 2 || mapper == 0 || mapper == 3)
        mode[1:0] <= flags[14] ? 2'b10 : 2'b11;
        
      // UNROM #2 - Current bank in $8000-$BFFF and fixed top half of outer bank in $C000-$FFFF
      if (mapper == 2) begin
        mode[5:2] <= 4'b1111; // 256K banks, UNROM mode
      end
		
      // CNROM #3 - Fixed PRG bank, switchable CHR bank.
      if (mapper == 3)
        selreg <= 0;

      // AxROM #7 - Switch 32kb rom bank + switchable nametables
      if (mapper == 7) begin
        mode[1:0] <= 2'b00;   // Switchable VRAM page.
        mode[5:2] <= 4'b1100; // 256K banks, (B)NROM mode
		  outer[5:0] <= 6'h00;
      end
    end else if (ce) begin
      if ((prg_ain[15:12] == 4'h5) & prg_write && allow_select)
			selreg <= {prg_din[7], prg_din[0]};        // select register
      if (prg_ain[15] & prg_write) begin
        case (selreg)
        2'h0:  {mode[0], a53chr}  <= {(mode[1] ? mode[0] : prg_din[4]), prg_din[1:0]};  // CHR RAM bank
        2'h1:  {mode[0], inner}   <= {(mode[1] ? mode[0] : prg_din[4]), prg_din[3:0]};  // "inner" bank
        2'h2:  {mode}             <= {prg_din[5:0]};                                    // mode register
        2'h3:  {outer}            <= {prg_din[5:0]};                                    // "outer" bank
        endcase
      end
    end
    
    always begin
      // mirroring mode
      casez(mode[1:0])
      2'b0?   :   vram_a10 = {mode[0]};        // 1 screen lower
      2'b10   :   vram_a10 = {chr_ain[10]};    // vertical
      2'b11   :   vram_a10 = {chr_ain[11]};    // horizontal
      endcase

      // PRG ROM bank size select
      casez({mode[5:2], prg_ain[14]})
      5'b00_0?_?  :  a53prg = {outer[5:0],             prg_ain[14]};  // 32K banks, (B)NROM mode
      5'b01_0?_?  :  a53prg = {outer[5:1], inner[0],   prg_ain[14]};  // 64K banks, (B)NROM mode
      5'b10_0?_?  :  a53prg = {outer[5:2], inner[1:0], prg_ain[14]};  // 128K banks, (B)NROM mode
      5'b11_0?_?  :  a53prg = {outer[5:3], inner[2:0], prg_ain[14]};  // 256K banks, (B)NROM mode
      
      5'b00_10_1,
      5'b00_11_0  :  a53prg = {outer[5:0], inner[0]};             // 32K banks, UNROM mode
      5'b01_10_1,
      5'b01_11_0  :  a53prg = {outer[5:1], inner[1:0]};           // 64K banks, UNROM mode
      5'b10_10_1,
      5'b10_11_0  :  a53prg = {outer[5:2], inner[2:0]};           // 128K banks, UNROM mode
      5'b11_10_1,
      5'b11_11_0  :  a53prg = {outer[5:3], inner[3:0]};           // 256K banks, UNROM mode
      
      default     :  a53prg = {outer[5:0],             prg_ain[14]};  // 16K fixed bank
      endcase
    end

  assign vram_ce = chr_ain[13];
  assign prg_aout = {1'b0, (a53prg & 7'b0011111), prg_ain[13:0]};
  assign prg_allow = prg_ain[15] && !prg_write;
  assign chr_allow = flags[15];
  assign chr_aout = {7'b10_0000_0, a53chr, chr_ain[12:0]};
endmodule

// Mapper 42, used for hacked FDS games converted to cartridge form
module Mapper42(input clk, input ce, input reset,
            input [31:0] flags,
            input [15:0] prg_ain, output [21:0] prg_aout,
            input prg_read, prg_write,                   // Read / write signals
            input [7:0] prg_din,
            output prg_allow,                            // Enable access to memory for the specified operation.
            input [13:0] chr_ain, output [21:0] chr_aout,
            output chr_allow,                      		// Allow write
            output vram_a10,                             // Value for A10 address line
            output vram_ce,                     			// True if the address should be routed to the internal 2kB VRAM.
				output reg irq); 

	reg [3:0] prg_bank;
	reg [3:0] chr_bank;
	reg [3:0] prg_sel;
	reg mirroring;
	reg irq_enable;
	reg [14:0] irq_counter;
	
	always @(posedge clk) if (reset) begin
		prg_bank <= 0;
		chr_bank <= 0;
		mirroring <= flags[14];
		irq_counter <= 0;
	end else if (ce) begin
		if (prg_write)
			case(prg_ain & 16'he003)
			16'h8000: chr_bank <= prg_din[3:0];
			16'he000: prg_bank <= prg_din[3:0];
			16'he001: mirroring <= prg_din[3];
			16'he002: irq_enable <= prg_din[1];
			endcase

		if (irq_enable)
			irq_counter <= irq_counter + 15'd1;
		else begin
			irq <= 1'b0;	// ACK
			irq_counter <= 0;
		end	
		
		if (irq_counter == 15'h6000)
			irq <= 1'b1;
			
	end
	
	always @* begin
/* PRG bank selection
	6000-7FFF: Selectable
	8000-9FFF: bank #0Ch
	A000-BFFF: bank #0Dh
	C000-DFFF: bank #0Eh
	E000-FFFF: bank #0Fh
*/	
		case(prg_ain[15:13])
		3'b011: 	prg_sel = prg_bank;                // $6000-$7FFF
		3'b100: 	prg_sel = 4'hC;
		3'b101: 	prg_sel = 4'hD;
		3'b110: 	prg_sel = 4'hE;
		3'b111: 	prg_sel = 4'hF;
		endcase
	end 
	assign prg_aout = {5'b0, prg_sel, prg_ain[12:0]};    		// 8kB banks
	assign chr_aout = {5'b10_000, chr_bank, chr_ain[12:0]};	// 8kB banks

	assign prg_allow = (prg_ain >= 16'h6000) && !prg_write;
	assign chr_allow = flags[15];
	assign vram_ce = chr_ain[13];
	assign vram_a10 = mirroring ? chr_ain[10] : chr_ain[11];
endmodule

// 11 - Color Dreams
// 66 - GxROM
module Mapper66(input clk, input ce, input reset,
                input [31:0] flags,
                input [15:0] prg_ain, output [21:0] prg_aout,
                input prg_read, prg_write,                   // Read / write signals
                input [7:0] prg_din,
                output prg_allow,                            // Enable access to memory for the specified operation.
                input [13:0] chr_ain, output [21:0] chr_aout,
                output chr_allow,                      // Allow write
                output vram_a10,                             // Value for A10 address line
                output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.
  reg [1:0] prg_bank;
  reg [3:0] chr_bank;
  wire GXROM = (flags[7:0] == 66);
  always @(posedge clk) if (reset) begin
    prg_bank <= 0;
    chr_bank <= 0;
  end else if (ce) begin
    if (prg_ain[15] & prg_write) begin
      if (GXROM)
        {prg_bank, chr_bank} <= {prg_din[5:4], 2'b0, prg_din[1:0]};
      else // Color Dreams
        {chr_bank, prg_bank} <= {prg_din[7:4], prg_din[1:0]};
    end
  end
  assign prg_aout = {5'b00_000, prg_bank, prg_ain[14:0]};
  assign prg_allow = prg_ain[15] && !prg_write;
  assign chr_allow = flags[15];
  assign chr_aout = {5'b10_000, chr_bank, chr_ain[12:0]};
  assign vram_ce = chr_ain[13];
  assign vram_a10 = flags[14] ? chr_ain[10] : chr_ain[11];
endmodule

// 34 - BxROM or NINA-001
module Mapper34(input clk, input ce, input reset,
                input [31:0] flags,
                input [15:0] prg_ain, output [21:0] prg_aout,
                input prg_read, prg_write,                   // Read / write signals
                input [7:0] prg_din,
                output prg_allow,                            // Enable access to memory for the specified operation.
                input [13:0] chr_ain, output [21:0] chr_aout,
                output chr_allow,                      // Allow write
                output vram_a10,                             // Value for A10 address line
                output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.
  reg [1:0] prg_bank;
  reg [3:0] chr_bank_0, chr_bank_1;
  
  wire NINA = (flags[13:11] != 0); // NINA is used when there is more than 8kb of CHR
  always @(posedge clk) if (reset) begin
    prg_bank <= 0;
    chr_bank_0 <= 0;
    chr_bank_1 <= 1; // To be compatible with BxROM
  end else if (ce && prg_write) begin
    if (!NINA) begin // BxROM
      if (prg_ain[15])
        prg_bank <= prg_din[1:0];
    end else begin // NINA
      if (prg_ain == 16'h7ffd)
        prg_bank <= prg_din[1:0];
      else if (prg_ain == 16'h7ffe)
        chr_bank_0 <= prg_din[3:0];
      else if (prg_ain == 16'h7fff)
        chr_bank_1 <= prg_din[3:0];
    end
  end

  wire [21:0] prg_aout_tmp = {5'b00_000, prg_bank, prg_ain[14:0]};
  assign chr_allow = flags[15];
  assign chr_aout = {6'b10_0000, chr_ain[12] == 0 ? chr_bank_0 : chr_bank_1, chr_ain[11:0]};
  assign vram_ce = chr_ain[13];
  assign vram_a10 = flags[14] ? chr_ain[10] : chr_ain[11];

  wire prg_is_ram = (prg_ain >= 'h6000 && prg_ain < 'h8000) && NINA;
  assign prg_allow = prg_ain[15] && !prg_write ||
                     prg_is_ram;
  wire [21:0] prg_ram = {9'b11_1100_000, prg_ain[12:0]};
  assign prg_aout = prg_is_ram ? prg_ram : prg_aout_tmp;
endmodule

// 41 - Caltron 6-in-1
module Mapper41(input clk, input ce, input reset,
                input [31:0] flags,
                input [15:0] prg_ain, output [21:0] prg_aout,
                input prg_read, prg_write,                   // Read / write signals
                input [7:0] prg_din,
                output prg_allow,                            // Enable access to memory for the specified operation.
                input [13:0] chr_ain, output [21:0] chr_aout,
                output chr_allow,                      // Allow write
                output vram_a10,                             // Value for A10 address line
                output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.
  reg [2:0] prg_bank;
  reg [1:0] chr_outer_bank, chr_inner_bank;
  reg mirroring;
  
  always @(posedge clk) if (reset) begin
    prg_bank <= 0;
    chr_outer_bank <= 0;
    chr_inner_bank <= 0;
    mirroring <= 0;
  end else if (ce && prg_write) begin
    if (prg_ain[15:11] == 5'b01100) begin
      {mirroring, chr_outer_bank, prg_bank} <= prg_ain[5:0];
    end else if (prg_ain[15] && prg_bank[2]) begin
      // The Inner CHR Bank Select only can be written while the PRG ROM bank is 4, 5, 6, or 7
      chr_inner_bank <= prg_din[1:0];
    end
  end

  assign prg_aout = {4'b00_00, prg_bank, prg_ain[14:0]};
  assign chr_allow = flags[15];
  assign chr_aout = {5'b10_000, chr_outer_bank, chr_inner_bank, chr_ain[12:0]};
  assign vram_ce = chr_ain[13];
  assign vram_a10 = mirroring ? chr_ain[11] : chr_ain[10];
  assign prg_allow = prg_ain[15] && !prg_write;
endmodule

// #68 - Sunsoft-4 - Game After Burner, and some japanese games. MAX: 128kB PRG, 256kB CHR
module Mapper68(input clk, input ce, input reset,
                input [31:0] flags,
                input [15:0] prg_ain, output [21:0] prg_aout,
                input prg_read, prg_write,                   // Read / write signals
                input [7:0] prg_din,
                output prg_allow,                            // Enable access to memory for the specified operation.
                input [13:0] chr_ain, output [21:0] chr_aout,
                output chr_allow,                      // Allow write
                output vram_a10,                             // Value for A10 address line
                output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.
  reg [6:0] chr_bank_0, chr_bank_1, chr_bank_2, chr_bank_3;
  reg [6:0] nametable_0, nametable_1;
  reg [2:0] prg_bank;
  reg use_chr_rom;
  reg mirroring;
  always @(posedge clk) if (reset) begin
    chr_bank_0 <= 0;
    chr_bank_1 <= 0;
    chr_bank_2 <= 0;
    chr_bank_3 <= 0;
    nametable_0 <= 0;
    nametable_1 <= 0;
    prg_bank <= 0;
    use_chr_rom <= 0;
    mirroring <= 0;
  end else if (ce) begin
    if (prg_ain[15] && prg_write) begin
//      $write("REG[%d] <= %X\n", prg_ain[14:12], prg_din);
      case(prg_ain[14:12])
      0: chr_bank_0  <= prg_din[6:0]; // $8000-$8FFF: 2kB CHR bank at $0000
      1: chr_bank_1  <= prg_din[6:0]; // $9000-$9FFF: 2kB CHR bank at $0800
      2: chr_bank_2  <= prg_din[6:0]; // $A000-$AFFF: 2kB CHR bank at $1000
      3: chr_bank_3  <= prg_din[6:0]; // $B000-$BFFF: 2kB CHR bank at $1800
      4: nametable_0 <= prg_din[6:0]; // $C000-$CFFF: 1kB Nametable register 0 at $2000
      5: nametable_1 <= prg_din[6:0]; // $D000-$DFFF: 1kB Nametable register 1 at $2400
      6: {use_chr_rom, mirroring} <= {prg_din[4], prg_din[0]};  // $E000-$EFFF: Nametable control
      7: prg_bank <= prg_din[2:0]; 
      endcase
    end
  end
  wire [2:0] prgout = (prg_ain[14] ? 3'b111 : prg_bank);
  assign prg_aout = {5'b00_000, prgout, prg_ain[13:0]};
  assign prg_allow = prg_ain[15] && !prg_write;

  reg [6:0] chrout;  
  always begin
    casez(chr_ain[12:11])
    0: chrout = chr_bank_0;
    1: chrout = chr_bank_1;
    2: chrout = chr_bank_2;
    3: chrout = chr_bank_3;
    endcase
  end
  assign vram_a10 = mirroring ? chr_ain[11] : chr_ain[10];
  wire [6:0] nameout = (vram_a10 == 0) ? nametable_0 : nametable_1;
 
  assign chr_allow = flags[15];
  assign chr_aout = (chr_ain[13] == 0) ? {4'b10_00, chrout, chr_ain[10:0]} : {5'b10_001, nameout, chr_ain[9:0]};
  assign vram_ce = chr_ain[13] && !use_chr_rom;

endmodule

// 69 - Sunsoft FME-7
module Mapper69(input clk, input ce, input reset,
                input [31:0] flags,
                input [15:0] prg_ain, output [21:0] prg_aout,
                input prg_read, prg_write,                   // Read / write signals
                input [7:0] prg_din,
                output prg_allow,                          // Enable access to memory for the specified operation.
                input [13:0] chr_ain, output [21:0] chr_aout,
                output chr_allow,                             // Allow write
                output reg vram_a10,                          // Value for A10 address line
                output vram_ce,                               // True if the address should be routed to the internal 2kB VRAM.
                output reg irq);
  reg [7:0] chr_bank[0:7];
  reg [4:0] prg_bank[0:3];
  reg [1:0] mirroring;
  reg irq_countdown, irq_trigger;
  reg [15:0] irq_counter;
  reg [3:0] addr;
  reg ram_enable, ram_select;
  wire [16:0] new_irq_counter = irq_counter - {15'b0, irq_countdown};
  always @(posedge clk) if (reset) begin
    chr_bank[0] <= 0;
    chr_bank[1] <= 0;
    chr_bank[2] <= 0;
    chr_bank[3] <= 0;
    chr_bank[4] <= 0;
    chr_bank[5] <= 0;
    chr_bank[6] <= 0;
    chr_bank[7] <= 0;
    prg_bank[0] <= 0;
    prg_bank[1] <= 0;
    prg_bank[2] <= 0;
    prg_bank[3] <= 0;
    mirroring <= 0;
    irq_countdown <= 0;
    irq_trigger <= 0;
    irq_counter <= 0;
    addr <= 0;
    ram_enable <= 0;
    ram_select <= 0;
    irq <= 0;
  end else if (ce) begin
    irq_counter <= new_irq_counter[15:0];
    if (irq_trigger && new_irq_counter[16]) irq <= 1;
    if (!irq_trigger) irq <= 0;
      
    if (prg_ain[15] & prg_write) begin
      case (prg_ain[14:13])
      0: addr <= prg_din[3:0];
      1: begin
          case(addr)
          0,1,2,3,4,5,6,7: chr_bank[addr[2:0]] <= prg_din;
          8,9,10,11:       prg_bank[addr[1:0]] <= prg_din[4:0];
          12:              mirroring <= prg_din[1:0];
          13:              {irq_countdown, irq_trigger} <= {prg_din[7], prg_din[0]};
          14:              irq_counter[7:0] <= prg_din;
          15:              irq_counter[15:8] <= prg_din;
          endcase
          if (addr == 8) {ram_enable, ram_select} <= prg_din[7:6];
        end
      endcase
    end
  end
  always begin
    casez(mirroring[1:0])
    2'b00   :   vram_a10 = {chr_ain[10]};    // vertical
    2'b01   :   vram_a10 = {chr_ain[11]};    // horizontal
    2'b1?   :   vram_a10 = {mirroring[0]};   // 1 screen lower
    endcase
  end
  reg [4:0] prgout;
  reg [7:0] chrout;
  always begin
    casez(prg_ain[15:13])
    3'b011:  prgout = prg_bank[0];
    3'b100:  prgout = prg_bank[1];
    3'b101:  prgout = prg_bank[2];
    3'b110:  prgout = prg_bank[3];
    3'b111:  prgout = 5'b11111;
    default: prgout = 5'bxxxxx;
    endcase
    chrout = chr_bank[chr_ain[12:10]];
  end
  wire ram_cs = (prg_ain[15] == 0 && ram_select);
  assign prg_aout = {1'b0, ram_cs, 2'b00, prgout[4:0], prg_ain[12:0]};
  assign prg_allow = ram_cs ? ram_enable : !prg_write;
  assign chr_allow = flags[15];
  assign chr_aout = {4'b10_00, chrout, chr_ain[9:0]};
  assign vram_ce = chr_ain[13];
endmodule

// #71,#232 - Camerica
module Mapper71(input clk, input ce, input reset,
                input [31:0] flags,
                input [15:0] prg_ain, output [21:0] prg_aout,
                input prg_read, prg_write,                   // Read / write signals
                input [7:0] prg_din,
                output prg_allow,                            // Enable access to memory for the specified operation.
                input [13:0] chr_ain, output [21:0] chr_aout,
                output chr_allow,                      // Allow write
                output vram_a10,                             // Value for A10 address line
                output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.
  reg [3:0] prg_bank;
  reg ciram_select;
  wire mapper232 = (flags[7:0] == 232);
  always @(posedge clk) if (reset) begin
    prg_bank <= 0;
    ciram_select <= 0;
  end else if (ce) begin
    if (prg_ain[15] && prg_write) begin
      $write("%X <= %X (bank = %x)\n", prg_ain, prg_din, prg_bank);
      if (!prg_ain[14] && mapper232) // $8000-$BFFF Outer bank select (only on iNES 232)
        prg_bank[3:2] <= prg_din[4:3];
      if (prg_ain[14:13] == 0)       // $8000-$9FFF Fire Hawk Mirroring
        ciram_select <= prg_din[4];
      if (prg_ain[14])               // $C000-$FFFF Bank select
        prg_bank <= {mapper232 ? prg_bank[3:2] : prg_din[3:2], prg_din[1:0]};
    end
  end
  reg [3:0] prgout;
  always begin
    casez({prg_ain[14], mapper232})
    2'b0?: prgout = prg_bank;
    2'b10: prgout = 4'b1111;
    2'b11: prgout = {prg_bank[3:2], 2'b11};
    endcase
  end
  assign prg_aout = {4'b00_00, prgout, prg_ain[13:0]};
  assign prg_allow = prg_ain[15] && !prg_write;
  assign chr_allow = flags[15];
  assign chr_aout = {9'b10_0000_000, chr_ain[12:0]};
  assign vram_ce = chr_ain[13];
  // XXX(ludde): Fire hawk uses flags[14] == 0 while no other game seems to do that.
  // So when flags[14] == 0 we use ciram_select instead.
  assign vram_a10 = flags[14] ? chr_ain[10] : ciram_select;
endmodule

// #79,#113 - NINA-03 / NINA-06
module Mapper79(input clk, input ce, input reset,
                input [31:0] flags,
                input [15:0] prg_ain, output [21:0] prg_aout,
                input prg_read, prg_write,                   // Read / write signals
                input [7:0] prg_din,
                output prg_allow,                            // Enable access to memory for the specified operation.
                input [13:0] chr_ain, output [21:0] chr_aout,
                output chr_allow,                      // Allow write
                output vram_a10,                             // Value for A10 address line
                output vram_ce);                             // True if the address should be routed to the internal 2kB VRAM.
  reg [2:0] prg_bank;
  reg [3:0] chr_bank;
  reg mirroring;  // 0: Horizontal, 1: Vertical
  wire mapper113 = (flags[7:0] == 113); // NINA-06
  always @(posedge clk) if (reset) begin
    prg_bank <= 0;
    chr_bank <= 0;
    mirroring <= 0;
  end else if (ce) begin
    if (prg_ain[15:13] == 3'b010 && prg_ain[8] && prg_write)
      {mirroring, chr_bank[3], prg_bank, chr_bank[2:0]} <= prg_din;
  end
  assign prg_aout = {4'b00_00, prg_bank, prg_ain[14:0]};
  assign prg_allow = prg_ain[15] && !prg_write;
  assign chr_allow = flags[15];
  assign chr_aout = {5'b10_000, chr_bank, chr_ain[12:0]};
  assign vram_ce = chr_ain[13];
  wire mirrconfig = mapper113 ? mirroring : flags[14]; // Mapper #13 has mapper controlled mirroring
  assign vram_a10 = mirrconfig ? chr_ain[10] : chr_ain[11]; // 0: horiz, 1: vert
endmodule

// #105 - NES-EVENT. Retrofits an MMC3 with lots of extra logic.
module NesEvent(input clk, input ce, input reset,
                input [15:0] prg_ain, output reg [21:0] prg_aout,
                input [13:0] chr_ain, output [21:0] chr_aout,
                input [3:0] mmc1_chr,                   // Upper 4 CHR output control bits from MMC chip
                input [21:0] mmc1_aout,                 // PRG output address from MMC chip
                output irq);
  // $A000-BFFF:   [...I OAA.]
  //      I = IRQ control / initialization toggle
  //      O = PRG Mode/Chip select
  //      A = PRG Reg 'A'
  // Mapper gets "initialized" by setting I bit to 0 then to 1.
  // On powerup and reset, the first 32k of PRG (from the first PRG chip) is selected at $8000 *no matter what*.
  // PRG cannot be swapped until the mapper has been "initialized" by setting the 'I' bit to 0, then to '1'.  This
  // toggling will "unlock" PRG swapping on the mapper.
  reg unlocked, old_val;
  reg [29:0] counter;
  
  reg [3:0] oldbits;
  always @(posedge clk) if (reset) begin
    old_val <= 0;
    unlocked <= 0;
    counter <= 0;
  end else if (ce) begin
    // Handle unlock.
    if (mmc1_chr[3] && !old_val) unlocked <= 1;
    old_val <= mmc1_chr[3];
    // The 'I' bit in $A000 controls the IRQ counter.  When cleared, the IRQ counter counts up every cycle.  When
    // set, the IRQ counter is reset to 0 and stays there (does not count), and the pending IRQ is acknowledged.
    counter <= mmc1_chr[3] ? 0 : counter + 1;
    
    if (mmc1_chr != oldbits) begin
      $write("NESEV Control Bits: %X => %X (%d)\n", oldbits, mmc1_chr, unlocked);
      oldbits <= mmc1_chr;
    end
  end
  // In the official tournament, 'C' was closed, and the others were open, so the counter had to reach $2800000.
  assign irq = (counter[29:25] == 5'b10100);
  always begin
    if (!prg_ain[15]) begin
      // WRAM is always routed as usual.
      prg_aout = mmc1_aout; 
    end else if (!unlocked) begin
      // Not initialized yet, mapper switch disabled.
      prg_aout = {7'b00_0000_0, prg_ain[14:0]}; 
    end else if (mmc1_chr[2] == 0) begin
      // O=0:  Use first PRG chip (first 128k), use 'A' PRG Reg, 32k swap
      prg_aout = {5'b00_000, mmc1_chr[1:0], prg_ain[14:0]};
    end else begin
      // O=1:  Use second PRG chip (second 128k), use 'B' PRG Reg, MMC1 style swap
      prg_aout = mmc1_aout;
    end
  end
  // 8kB CHR RAM.
  assign chr_aout = {9'b10_0000_000, chr_ain[12:0]};
endmodule

// mapper 165
module Mapper165(input clk, input ce, input reset,
            input [31:0] flags,
            input [15:0] prg_ain, output [21:0] prg_aout,
            input prg_read, prg_write,                   // Read / write signals
            input [7:0] prg_din,
            output prg_allow,                            // Enable access to memory for the specified operation.
            input chr_read, input [13:0] chr_ain, output [21:0] chr_aout,
            output chr_allow,                            // Allow write
            output vram_a10,                             // Value for A10 address line
            output vram_ce,                              // True if the address should be routed to the internal 2kB VRAM.
            output reg irq);
  reg [2:0] bank_select;             // Register to write to next
  reg prg_rom_bank_mode;             // Mode for PRG banking
  reg chr_a12_invert;                // Mode for CHR banking
  reg mirroring;                     // 0 = vertical, 1 = horizontal
  reg irq_enable, irq_reload;        // IRQ enabled, and IRQ reload requested
  reg [7:0] irq_latch, counter;      // IRQ latch value and current counter
  reg ram_enable, ram_protect;       // RAM protection bits
  reg [5:0] prg_bank_0, prg_bank_1;  // Selected PRG banks
  wire prg_is_ram;

  reg [6:0] chr_bank_0, chr_bank_1;  // Selected CHR banks
  reg [7:0] chr_bank_2, chr_bank_3, chr_bank_4, chr_bank_5;
  reg latch_0, latch_1;
  
  wire [7:0] new_counter = (counter == 0 || irq_reload) ? irq_latch : counter - 1;
  reg [3:0] a12_ctr; 
   
  always @(posedge clk) if (reset) begin
    irq <= 0;
    bank_select <= 0;
    prg_rom_bank_mode <= 0;
    chr_a12_invert <= 0;
    mirroring <= flags[14];
    {irq_enable, irq_reload} <= 0;
    {irq_latch, counter} <= 0;
    {ram_enable, ram_protect} <= 0;
    {chr_bank_0, chr_bank_1, chr_bank_2, chr_bank_3, chr_bank_4, chr_bank_5} <= 0;
    {prg_bank_0, prg_bank_1} <= 0;
    a12_ctr <= 0;
  end else if (ce) begin
  
    if (prg_write && prg_ain[15]) begin
      case({prg_ain[14], prg_ain[13], prg_ain[0]})
      3'b00_0: {chr_a12_invert, prg_rom_bank_mode, bank_select} <= {prg_din[7], prg_din[6], prg_din[2:0]}; // Bank select ($8000-$9FFE, even)
      3'b00_1: begin // Bank data ($8001-$9FFF, odd)
        case (bank_select) 
        0: chr_bank_0 <= prg_din[7:1];  // Select 2 KB CHR bank at PPU $0000-$07FF (or $1000-$17FF);
        1: chr_bank_1 <= prg_din[7:1];  // Select 2 KB CHR bank at PPU $0800-$0FFF (or $1800-$1FFF);
        2: chr_bank_2 <= prg_din;       // Select 1 KB CHR bank at PPU $1000-$13FF (or $0000-$03FF);
        3: chr_bank_3 <= prg_din;       // Select 1 KB CHR bank at PPU $1400-$17FF (or $0400-$07FF);
        4: chr_bank_4 <= prg_din;       // Select 1 KB CHR bank at PPU $1800-$1BFF (or $0800-$0BFF);
        5: chr_bank_5 <= prg_din;       // Select 1 KB CHR bank at PPU $1C00-$1FFF (or $0C00-$0FFF);
        6: prg_bank_0 <= prg_din[5:0];  // Select 8 KB PRG ROM bank at $8000-$9FFF (or $C000-$DFFF);
        7: prg_bank_1 <= prg_din[5:0];  // Select 8 KB PRG ROM bank at $A000-$BFFF
        endcase
      end
      3'b01_0: mirroring <= prg_din[0];                   // Mirroring ($A000-$BFFE, even)
      3'b01_1: {ram_enable, ram_protect} <= prg_din[7:6]; // PRG RAM protect ($A001-$BFFF, odd)
      3'b10_0: irq_latch <= prg_din;                      // IRQ latch ($C000-$DFFE, even)
      3'b10_1: irq_reload <= 1;                           // IRQ reload ($C001-$DFFF, odd)
      3'b11_0: begin irq_enable <= 0; irq <= 0; end       // IRQ disable ($E000-$FFFE, even)
      3'b11_1: irq_enable <= 1;                           // IRQ enable ($E001-$FFFF, odd)
      endcase
    end

    // Trigger IRQ counter on rising edge of chr_ain[12]
    // All MMC3A's and non-Sharp MMC3B's will generate only a single IRQ when $C000 is $00.
    // This is because this version of the MMC3 generates IRQs when the scanline counter is decremented to 0.
    // In addition, writing to $C001 with $C000 still at $00 will result in another single IRQ being generated.
    // In the community, this is known as the "alternate" or "old" behavior.
    // All MMC3C's and Sharp MMC3B's will generate an IRQ on each scanline while $C000 is $00.
    // This is because this version of the MMC3 generates IRQs when the scanline counter is equal to 0.
    // In the community, this is known as the "normal" or "new" behavior.
    if (chr_ain[12] && a12_ctr == 0) begin
      counter <= new_counter;
      if ( (counter != 0 || irq_reload) && new_counter == 0 && irq_enable) begin
//        $write("MMC3 SCANLINE IRQ!\n");
        irq <= 1;
      end
      irq_reload <= 0;      
    end
    a12_ctr <= chr_ain[12] ? 4'b1111 : (a12_ctr != 0) ? a12_ctr - 4'b0001 : a12_ctr;
  end

  // The PRG bank to load. Each increment here is 8kb. So valid values are 0..63.
  reg [5:0] prgsel;
  always @* begin
    casez({prg_ain[14:13], prg_rom_bank_mode})
    3'b00_0: prgsel = prg_bank_0;  // $8000 mode 0
    3'b00_1: prgsel = 6'b111110;   // $8000 fixed to second last bank
    3'b01_?: prgsel = prg_bank_1;  // $A000 mode 0,1
    3'b10_0: prgsel = 6'b111110;   // $C000 fixed to second last bank
    3'b10_1: prgsel = prg_bank_0;  // $C000 mode 1
    3'b11_?: prgsel = 6'b111111;   // $E000 fixed to last bank
    endcase
  end
  wire [21:0] prg_aout_tmp = {3'b00_0,  prgsel, prg_ain[12:0]};

// PPU reads $0FD0: latch 0 is set to $FD for subsequent reads
// PPU reads $0FE0: latch 0 is set to $FE for subsequent reads
// PPU reads $1FD0 through $1FDF: latch 1 is set to $FD for subsequent reads
// PPU reads $1FE0 through $1FEF: latch 1 is set to $FE for subsequent reads
  always @(posedge clk) if (ce && chr_read) begin
    latch_0 <= (chr_ain & 14'h3fff) == 14'h0fd0 ? 0 : (chr_ain & 14'h3fff) == 14'h0fe0 ? 1 : latch_0;
    latch_1 <= (chr_ain & 14'h3ff0) == 14'h1fd0 ? 0 : (chr_ain & 14'h3ff0) == 14'h1fe0 ? 1 : latch_1;
  end

  // The CHR bank to load. Each increment here is 1kb. So valid values are 0..255.
  reg [7:0] chrsel;
  always @* begin
    casez({chr_ain[12] ^ chr_a12_invert, latch_0, latch_1})
    3'b0_0?: chrsel = {chr_bank_0, chr_ain[10]};	// 2Kb page
    3'b0_1?: chrsel = {chr_bank_1, chr_ain[10]};	// 2Kb page
    3'b1_?0: chrsel = chr_bank_2;
    3'b1_?1: chrsel = chr_bank_4;
    endcase
  end
  
  assign {chr_allow, chr_aout} = {flags[15] && (chrsel < 4), 4'b10_00, chrsel, chr_ain[9:0]};

  assign prg_is_ram = prg_ain >= 'h6000 && prg_ain < 'h8000 && ram_enable && !(ram_protect && prg_write);
  assign prg_allow = prg_ain[15] && !prg_write || prg_is_ram;
  wire [21:0] prg_ram = {9'b11_1100_000, prg_ain[12:0]};
  assign prg_aout = prg_is_ram ? prg_ram : prg_aout_tmp;
  assign vram_a10 = mirroring ? chr_ain[11] : chr_ain[10];  
  assign vram_ce = chr_ain[13];
endmodule

// iNES Mapper 228 represents the board used by Active Enterprises for Action 52 and Cheetahmen II.
module Mapper228(input clk, input ce, input reset,
                input [31:0] flags,
                input [15:0] prg_ain, output [21:0] prg_aout,
                input prg_read, prg_write,                   // Read / write signals
                input [7:0] prg_din,
                output prg_allow,                          // Enable access to memory for the specified operation.
                input [13:0] chr_ain, output [21:0] chr_aout,
                output chr_allow,                             // Allow write
                output vram_a10,                              // Value for A10 address line
                output vram_ce);                              // True if the address should be routed to the internal 2kB VRAM.
  reg mirroring;
  reg [1:0] prg_chip;
  reg [4:0] prg_bank;
  reg prg_bank_mode;
  reg [5:0] chr_bank;
  always @(posedge clk) if (reset) begin
    {mirroring, prg_chip, prg_bank, prg_bank_mode} <= 0;
    chr_bank <= 0;
  end else if (ce) begin
    if (prg_ain[15] & prg_write) begin
      {mirroring, prg_chip, prg_bank, prg_bank_mode} <= prg_ain[13:5];
      chr_bank <= {prg_ain[3:0], prg_din[1:0]};
    end
  end
  assign vram_a10 = mirroring ? chr_ain[11] : chr_ain[10];
  wire prglow = prg_bank_mode ? prg_bank[0] : prg_ain[14];
  wire [1:0] addrsel = {prg_chip[1], prg_chip[1] ^ prg_chip[0]};
  assign prg_aout = {1'b0, addrsel, prg_bank[4:1], prglow, prg_ain[13:0]};
  assign prg_allow = prg_ain[15] && !prg_write;
  assign chr_allow = flags[15];
  assign chr_aout = {3'b10_0, chr_bank, chr_ain[12:0]};
  assign vram_ce = chr_ain[13];
endmodule

module Mapper234(input clk, input ce, input reset,
                input [31:0] flags,
                input [15:0] prg_ain, output [21:0] prg_aout,
                input prg_read, prg_write,                   // Read / write signals
                input [7:0] prg_din,
                output prg_allow,                          // Enable access to memory for the specified operation.
                input [13:0] chr_ain, output [21:0] chr_aout,
                output chr_allow,                             // Allow write
                output vram_a10,                              // Value for A10 address line
                output vram_ce);                              // True if the address should be routed to the internal 2kB VRAM.
  reg [2:0] block, inner_chr;
  reg mode, mirroring, inner_prg;
  always @(posedge clk) if (reset) begin
    block <= 0;
    {mode, mirroring} <= 0;
    inner_chr <= 0;
    inner_prg <= 0;
  end else if (ce) begin
    if (prg_read && prg_ain[15:7] == 9'b1111_1111_1) begin
      // Outer bank control $FF80 - $FF9F
      if (prg_ain[6:0] < 7'h20 && (block == 0)) begin
        {mirroring, mode} <= prg_din[7:6];
        block <= prg_din[3:1];
        {inner_chr[2], inner_prg} <= {prg_din[0], prg_din[0]};
      end
      // Inner bank control ($FFE8-$FFF7)
      if (prg_ain[6:0] >= 7'h68 && prg_ain[6:0] < 7'h78) begin
        {inner_chr[2], inner_prg} <= mode ? {prg_din[6], prg_din[0]} : {inner_chr[2], inner_prg};
        inner_chr[1:0] <= prg_din[5:4];
      end
    end
  end
  assign vram_a10 = mirroring ? chr_ain[11] : chr_ain[10];
  assign prg_aout = {3'b00_0, block, inner_prg, prg_ain[14:0]};
  assign chr_aout = {3'b10_0, block, inner_chr, chr_ain[12:0]};
  assign prg_allow = prg_ain[15] && !prg_write;
  assign chr_allow = flags[15];
  assign vram_ce = chr_ain[13];
endmodule

module MultiMapper(input clk, input ce, input ppu_ce, input reset,
                   input [19:0] ppuflags,                           // Misc flags from PPU for MMC5 cheating
                   input [31:0] flags,                              // Misc flags from ines header {prg_size(3), chr_size(3), mapper(8)}
                   input [15:0] prg_ain, output reg [21:0] prg_aout,// PRG Input / Output Address Lines
                   input prg_read, prg_write,                       // PRG Read / write signals
                   input [7:0] prg_din, output reg [7:0] prg_dout,  // PRG Data
                   input [7:0] prg_from_ram,                        // PRG Data from RAM
                   output reg prg_allow,                            // PRG Allow write access
                   input chr_read,                                  // Read from CHR
                   input [13:0] chr_ain, output reg [21:0] chr_aout,// CHR Input / Output Address Lines
                   output reg [7:0] chr_dout,                       // Value to override CHR data with
                   output reg has_chr_dout,                         // True if CHR data should be overridden
                   output reg chr_allow,                            // CHR Allow write
                   output reg vram_a10,                             // CHR Value for A10 address line
                   output reg vram_ce,                              // CHR True if the address should be routed to the internal 2kB VRAM.
                   output reg irq);
  wire mmc0_prg_allow, mmc0_vram_a10, mmc0_vram_ce, mmc0_chr_allow;
  wire [21:0] mmc0_prg_addr, mmc0_chr_addr;
  MMC0 mmc0(clk, ce, flags, prg_ain, mmc0_prg_addr, prg_read, prg_write, prg_din, mmc0_prg_allow,
                            chr_ain, mmc0_chr_addr, mmc0_chr_allow, mmc0_vram_a10, mmc0_vram_ce);

  wire mmc1_prg_allow, mmc1_vram_a10, mmc1_vram_ce, mmc1_chr_allow;
  wire [21:0] mmc1_prg_addr, mmc1_chr_addr;
  MMC1 mmc1(clk, ce, reset, flags, prg_ain, mmc1_prg_addr, prg_read, prg_write, prg_din, mmc1_prg_allow,
                                   chr_ain, mmc1_chr_addr, mmc1_chr_allow, mmc1_vram_a10, mmc1_vram_ce);

  wire map28_prg_allow, map28_vram_a10, map28_vram_ce, map28_chr_allow;
  wire [21:0] map28_prg_addr, map28_chr_addr;
  Mapper28 map28(clk, ce, reset, flags, prg_ain, map28_prg_addr, prg_read, prg_write, prg_din, map28_prg_allow,
                                        chr_ain, map28_chr_addr, map28_chr_allow, map28_vram_a10, map28_vram_ce);

  /*wire mmc2_prg_allow, mmc2_vram_a10, mmc2_vram_ce, mmc2_chr_allow;
  wire [21:0] mmc2_prg_addr, mmc2_chr_addr;
  MMC2 mmc2(clk, ppu_ce, reset, flags, prg_ain, mmc2_prg_addr, prg_read, prg_write, prg_din, mmc2_prg_allow,
                                   chr_read, chr_ain, mmc2_chr_addr, mmc2_chr_allow, mmc2_vram_a10, mmc2_vram_ce);

  wire mmc3_prg_allow, mmc3_vram_a10, mmc3_vram_ce, mmc3_chr_allow, mmc3_irq;
  wire [21:0] mmc3_prg_addr, mmc3_chr_addr;
  MMC3 mmc3(clk, ppu_ce, reset, flags, prg_ain, mmc3_prg_addr, prg_read, prg_write, prg_din, mmc3_prg_allow,
                                   chr_ain, mmc3_chr_addr, mmc3_chr_allow, mmc3_vram_a10, mmc3_vram_ce, mmc3_irq);

  wire mmc4_prg_allow, mmc4_vram_a10, mmc4_vram_ce, mmc4_chr_allow;
  wire [21:0] mmc4_prg_addr, mmc4_chr_addr;
  MMC4 mmc4(clk, ppu_ce, reset, flags, prg_ain, mmc4_prg_addr, prg_read, prg_write, prg_din, mmc4_prg_allow,
                                   chr_read, chr_ain, mmc4_chr_addr, mmc4_chr_allow, mmc4_vram_a10, mmc4_vram_ce);

  wire mmc5_prg_allow, mmc5_vram_a10, mmc5_vram_ce, mmc5_chr_allow, mmc5_irq;
  wire [21:0] mmc5_prg_addr, mmc5_chr_addr;
  wire [7:0] mmc5_chr_dout, mmc5_prg_dout;
  wire mmc5_has_chr_dout;
  MMC5 mmc5(clk, ppu_ce, reset, flags, ppuflags, prg_ain, mmc5_prg_addr, prg_read, prg_write, prg_din, mmc5_prg_dout, mmc5_prg_allow,
                                   chr_ain, mmc5_chr_addr, mmc5_chr_dout, mmc5_has_chr_dout, 
                                   mmc5_chr_allow, mmc5_vram_a10, mmc5_vram_ce, mmc5_irq);

  wire map13_prg_allow, map13_vram_a10, map13_vram_ce, map13_chr_allow;
  wire [21:0] map13_prg_addr, map13_chr_addr;
  Mapper13 map13(clk, ce, reset, flags, prg_ain, map13_prg_addr, prg_read, prg_write, prg_din, map13_prg_allow,
                                        chr_ain, map13_chr_addr, map13_chr_allow, map13_vram_a10, map13_vram_ce);

  wire map15_prg_allow, map15_vram_a10, map15_vram_ce, map15_chr_allow;
  wire [21:0] map15_prg_addr, map15_chr_addr;
  Mapper15 map15(clk, ce, reset, flags, prg_ain, map15_prg_addr, prg_read, prg_write, prg_din, map15_prg_allow,
                                        chr_ain, map15_chr_addr, map15_chr_allow, map15_vram_a10, map15_vram_ce);

  wire map16_prg_allow, map16_vram_a10, map16_vram_ce, map16_chr_allow, map16_irq;
  wire [21:0] map16_prg_addr, map16_chr_addr;
  wire [7:0] map16_prg_dout;
  Mapper16 map16(clk, ce, reset, flags, prg_ain, map16_prg_addr, prg_read, prg_write, prg_din, map16_prg_dout, map16_prg_allow,
                                        chr_ain, map16_chr_addr, map16_chr_allow, map16_vram_a10, map16_vram_ce, map16_irq);

  wire map34_prg_allow, map34_vram_a10, map34_vram_ce, map34_chr_allow;
  wire [21:0] map34_prg_addr, map34_chr_addr;
  Mapper34 map34(clk, ce, reset, flags, prg_ain, map34_prg_addr, prg_read, prg_write, prg_din, map34_prg_allow,
                                        chr_ain, map34_chr_addr, map34_chr_allow, map34_vram_a10, map34_vram_ce);

  wire map41_prg_allow, map41_vram_a10, map41_vram_ce, map41_chr_allow;
  wire [21:0] map41_prg_addr, map41_chr_addr;
  Mapper41 map41(clk, ce, reset, flags, prg_ain, map41_prg_addr, prg_read, prg_write, prg_din, map41_prg_allow,
                                        chr_ain, map41_chr_addr, map41_chr_allow, map41_vram_a10, map41_vram_ce);

  wire map42_prg_allow, map42_vram_a10, map42_vram_ce, map42_chr_allow, map42_irq;
  wire [21:0] map42_prg_addr, map42_chr_addr;
  Mapper42 map42(clk, ce, reset, flags, prg_ain, map42_prg_addr, prg_read, prg_write, prg_din, map42_prg_allow,
                                        chr_ain, map42_chr_addr, map42_chr_allow, map42_vram_a10, map42_vram_ce, map42_irq);

  wire map66_prg_allow, map66_vram_a10, map66_vram_ce, map66_chr_allow;
  wire [21:0] map66_prg_addr, map66_chr_addr;
  Mapper66 map66(clk, ce, reset, flags, prg_ain, map66_prg_addr, prg_read, prg_write, prg_din, map66_prg_allow,
                                        chr_ain, map66_chr_addr, map66_chr_allow, map66_vram_a10, map66_vram_ce);

  wire map68_prg_allow, map68_vram_a10, map68_vram_ce, map68_chr_allow;
  wire [21:0] map68_prg_addr, map68_chr_addr;
  Mapper68 map68(clk, ce, reset, flags, prg_ain, map68_prg_addr, prg_read, prg_write, prg_din, map68_prg_allow,
                                        chr_ain, map68_chr_addr, map68_chr_allow, map68_vram_a10, map68_vram_ce);

  wire map69_prg_allow, map69_vram_a10, map69_vram_ce, map69_chr_allow, map69_irq;
  wire [21:0] map69_prg_addr, map69_chr_addr;
  Mapper69 map69(clk, ce, reset, flags, prg_ain, map69_prg_addr, prg_read, prg_write, prg_din, map69_prg_allow,
                                        chr_ain, map69_chr_addr, map69_chr_allow, map69_vram_a10, map69_vram_ce, map69_irq);

  wire map71_prg_allow, map71_vram_a10, map71_vram_ce, map71_chr_allow;
  wire [21:0] map71_prg_addr, map71_chr_addr;
  Mapper71 map71(clk, ce, reset, flags, prg_ain, map71_prg_addr, prg_read, prg_write, prg_din, map71_prg_allow,
                                        chr_ain, map71_chr_addr, map71_chr_allow, map71_vram_a10, map71_vram_ce);

  wire map79_prg_allow, map79_vram_a10, map79_vram_ce, map79_chr_allow;
  wire [21:0] map79_prg_addr, map79_chr_addr;
  Mapper79 map79(clk, ce, reset, flags, prg_ain, map79_prg_addr, prg_read, prg_write, prg_din, map79_prg_allow,
                                        chr_ain, map79_chr_addr, map79_chr_allow, map79_vram_a10, map79_vram_ce);

  wire map165_prg_allow, map165_vram_a10, map165_vram_ce, map165_chr_allow, map165_irq;
  wire [21:0] map165_prg_addr, map165_chr_addr;
  Mapper165 map165(clk, ppu_ce, reset, flags, prg_ain, map165_prg_addr, prg_read, prg_write, prg_din, map165_prg_allow,
													 chr_read, chr_ain, map165_chr_addr, map165_chr_allow, map165_vram_a10, map165_vram_ce, map165_irq);

  wire map228_prg_allow, map228_vram_a10, map228_vram_ce, map228_chr_allow;
  wire [21:0] map228_prg_addr, map228_chr_addr;
  Mapper228 map228(clk, ce, reset, flags, prg_ain, map228_prg_addr, prg_read, prg_write, prg_din, map228_prg_allow,
                                          chr_ain, map228_chr_addr, map228_chr_allow, map228_vram_a10, map228_vram_ce);


  wire map234_prg_allow, map234_vram_a10, map234_vram_ce, map234_chr_allow;
  wire [21:0] map234_prg_addr, map234_chr_addr;
  Mapper234 map234(clk, ce, reset, flags, prg_ain, map234_prg_addr, prg_read, prg_write, prg_from_ram, map234_prg_allow,
                                          chr_ain, map234_chr_addr, map234_chr_allow, map234_vram_a10, map234_vram_ce);

  wire rambo1_prg_allow, rambo1_vram_a10, rambo1_vram_ce, rambo1_chr_allow, rambo1_irq;
  wire [21:0] rambo1_prg_addr, rambo1_chr_addr;
  Rambo1 rambo1(clk, ce, reset, flags, prg_ain, rambo1_prg_addr, prg_read, prg_write, prg_din, rambo1_prg_allow,
                                   chr_ain, rambo1_chr_addr, rambo1_chr_allow, rambo1_vram_a10, rambo1_vram_ce, rambo1_irq);*/

  wire [21:0] nesev_prg_addr, nesev_chr_addr;
  wire nesev_irq;
  NesEvent nesev(clk, ce, reset, prg_ain, nesev_prg_addr, chr_ain, nesev_chr_addr, mmc1_chr_addr[16:13], mmc1_prg_addr, nesev_irq);
  
  // Mask 
  reg [5:0] prg_mask;
  reg [6:0] chr_mask;

  always @* begin
    case(flags[10:8])
    0: prg_mask = 6'b000000;
    1: prg_mask = 6'b000001;
    2: prg_mask = 6'b000011;
    3: prg_mask = 6'b000111;
    4: prg_mask = 6'b001111;
    5: prg_mask = 6'b011111;
    default: prg_mask = 6'b111111;
    endcase

    case(flags[13:11])
    0: chr_mask = 7'b0000000;
    1: chr_mask = 7'b0000001;
    2: chr_mask = 7'b0000011;
    3: chr_mask = 7'b0000111;
    4: chr_mask = 7'b0001111;
    5: chr_mask = 7'b0011111;
    6: chr_mask = 7'b0111111;
    7: chr_mask = 7'b1111111;
    endcase
    
    irq = 0;
    prg_dout = 8'hff;
    has_chr_dout = 0;
    chr_dout = mmc5_chr_dout;
// 0 = Working
// 1 = Working
// 2 = Working
// 3 = Working
// 4 = Working
// 5 = Working
// 7 = Working
// 9 = Working
// 10 = Working
// 11 = Working
// 13 = Working
// 15 = Working
// 16 = Working minus EEPROM support
// 28 = Working
// 34 = Working
// 41 = Working
// 42 = Working
// 47 = Working
// 64 = Tons of GFX bugs
// 66 = Working
// 68 = Working
// 69 = Working
// 71 = Working
// 79 = Working
// 105 = Working
// 113 = Working
// 118 = Working
// 119 = Working
// 158 = Tons of GFX bugs
// 165 = GFX corrupted
// 209 = Not Tested
// 228 = Working
// 234 = Not Tested        
    case(flags[7:0])
    1:  {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}      = {mmc1_prg_addr, mmc1_prg_allow, mmc1_chr_addr, mmc1_vram_a10, mmc1_vram_ce, mmc1_chr_allow};
    /*9:  {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}      = {mmc2_prg_addr, mmc2_prg_allow, mmc2_chr_addr, mmc2_vram_a10, mmc2_vram_ce, mmc2_chr_allow};
    118, // TxSROM connects A17 to CIRAM A10.
    119, // TQROM  uses the Nintendo MMC3 like other TxROM boards but uses the CHR bank number specially.
    47,  // Mapper 047 is a MMC3 multicart
	 206, // MMC3 w/o IRQ or WRAM support
    4:  {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow, irq} = {mmc3_prg_addr, mmc3_prg_allow, mmc3_chr_addr, mmc3_vram_a10, mmc3_vram_ce, mmc3_chr_allow, mmc3_irq};

    10: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}      = {mmc4_prg_addr, mmc4_prg_allow, mmc4_chr_addr, mmc4_vram_a10, mmc4_vram_ce, mmc4_chr_allow};
	 
    5:  {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow, has_chr_dout, prg_dout, irq} = {mmc5_prg_addr, mmc5_prg_allow, mmc5_chr_addr, mmc5_vram_a10, mmc5_vram_ce, mmc5_chr_allow, mmc5_has_chr_dout, mmc5_prg_dout, mmc5_irq};*/

    0,
    2,
    3,
    7,
    28: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}      = {map28_prg_addr, map28_prg_allow, map28_chr_addr, map28_vram_a10, map28_vram_ce, map28_chr_allow};

  /*  13: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}      = {map13_prg_addr, map13_prg_allow, map13_chr_addr, map13_vram_a10, map13_vram_ce, map13_chr_allow};
    15: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}      = {map15_prg_addr, map15_prg_allow, map15_chr_addr, map15_vram_a10, map15_vram_ce, map15_chr_allow};
	 
	 16: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow, prg_dout, irq} = {map16_prg_addr, map16_prg_allow, map16_chr_addr, map16_vram_a10, map16_vram_ce, map16_chr_allow, map16_prg_dout, map16_irq};
    
	 34: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}      = {map34_prg_addr, map34_prg_allow, map34_chr_addr, map34_vram_a10, map34_vram_ce, map34_chr_allow};
    41: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}      = {map41_prg_addr, map41_prg_allow, map41_chr_addr, map41_vram_a10, map41_vram_ce, map41_chr_allow};

    64,
    158: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow, irq} = {rambo1_prg_addr, rambo1_prg_allow, rambo1_chr_addr, rambo1_vram_a10, rambo1_vram_ce, rambo1_chr_allow, rambo1_irq};

	 42: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow, irq} = {map42_prg_addr, map42_prg_allow, map42_chr_addr, map42_vram_a10, map42_vram_ce, map42_chr_allow, map42_irq};

    11,
    66: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}      = {map66_prg_addr, map66_prg_allow, map66_chr_addr, map66_vram_a10, map66_vram_ce, map66_chr_allow};
    68: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}      = {map68_prg_addr, map68_prg_allow, map68_chr_addr, map68_vram_a10, map68_vram_ce, map68_chr_allow};
    69: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow, irq} = {map69_prg_addr, map69_prg_allow, map69_chr_addr, map69_vram_a10, map69_vram_ce, map69_chr_allow, map69_irq};

    71,
    232: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}     = {map71_prg_addr, map71_prg_allow, map71_chr_addr, map71_vram_a10, map71_vram_ce, map71_chr_allow};

    79,
    113: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}     = {map79_prg_addr, map79_prg_allow, map79_chr_addr, map79_vram_a10, map79_vram_ce, map79_chr_allow};

    105: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow, irq}= {nesev_prg_addr, mmc1_prg_allow, nesev_chr_addr, mmc1_vram_a10, mmc1_vram_ce, mmc1_chr_allow, nesev_irq};

    165: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow, irq} = {map165_prg_addr, map165_prg_allow, map165_chr_addr, map165_vram_a10, map165_vram_ce, map165_chr_allow, map165_irq};

    228: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}     = {map228_prg_addr, map228_prg_allow, map228_chr_addr, map228_vram_a10, map228_vram_ce, map228_chr_allow};
    234: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow}     = {map234_prg_addr, map234_prg_allow, map234_chr_addr, map234_vram_a10, map234_vram_ce, map234_chr_allow};*/
    default: {prg_aout, prg_allow, chr_aout, vram_a10, vram_ce, chr_allow} = {mmc0_prg_addr, mmc0_prg_allow, mmc0_chr_addr, mmc0_vram_a10, mmc0_vram_ce, mmc0_chr_allow};
    endcase
    if (prg_aout[21:20] == 2'b00)
      prg_aout[19:0] = {prg_aout[19:14] & prg_mask, prg_aout[13:0]};
    if (chr_aout[21:20] == 2'b10)
      chr_aout[19:0] = {chr_aout[19:13] & chr_mask, chr_aout[12:0]};
    // Remap the CHR address into VRAM, if needed.
    chr_aout = vram_ce ? {11'b11_0000_0000_0, vram_a10, chr_ain[9:0]} : chr_aout;
    prg_aout = (prg_ain < 'h2000) ? {11'b11_1000_0000_0, prg_ain[10:0]} : prg_aout;
    prg_allow = prg_allow || (prg_ain < 'h2000);
  end
endmodule

// PRG       = 0....
// CHR       = 10...
// CHR-VRAM  = 1100
// CPU-RAM   = 1110
// CARTRAM   = 1111
                 // Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.

module DiffCheck(input [14:0] rgb1, input [14:0] rgb2, output result);
  wire [5:0] r = rgb1[4:0] - rgb2[4:0];
  wire [5:0] g = rgb1[9:5] - rgb2[9:5];
  wire [5:0] b = rgb1[14:10] - rgb2[14:10];
  wire [6:0] t = $signed(r) + $signed(b);
  wire [6:0] gx = {g[5], g};
  wire [7:0] y = $signed(t) + $signed(gx);
  wire [6:0] u = $signed(r) - $signed(b);
  wire [7:0] v = $signed({g, 1'b0}) - $signed(t);
  // if y is inside (-24..24)
  wire y_inside = (y < 8'h18 || y >= 8'he8);
  // if u is inside (-4, 4)
  wire u_inside = (u < 7'h4 || u >= 7'h7c);
  // if v is inside (-6, 6)
  wire v_inside = (v < 8'h6 || v >= 8'hfA);
  assign result = !(y_inside && u_inside && v_inside);
endmodule

module InnerBlend(input [8:0] Op, input [4:0] A, input [4:0] B, input [4:0] C, output [4:0] O);
  wire OpOnes = Op[4];
  wire [7:0] Amul = A * Op[7:5];
  wire [6:0] Bmul = B * Op[3:2];
  wire [6:0] Cmul = C * Op[1:0];
  wire [7:0] At =  Amul;
  wire [7:0] Bt = (OpOnes == 0) ? {Bmul, 1'b0} : {3'b0, B};
  wire [7:0] Ct = (OpOnes == 0) ? {Cmul, 1'b0} : {3'b0, C};
  wire [8:0] Res = {At, 1'b0} + Bt + Ct;
  assign O = Op[8] ? A : Res[8:4];
endmodule

module Blend(input [5:0] rule, input disable_hq2x,
             input [14:0] E, input [14:0] A, input [14:0] B, input [14:0] D, input [14:0] F, input [14:0] H, output [14:0] Result);
  reg [1:0] input_ctrl;
  reg [8:0] op;
  localparam BLEND0 = 9'b1_xxx_x_xx_xx; // 0: A
  localparam BLEND1 = 9'b0_110_0_10_00; // 1: (A * 12 + B * 4) >> 4
  localparam BLEND2 = 9'b0_100_0_10_10; // 2: (A * 8 + B * 4 + C * 4) >> 4
  localparam BLEND3 = 9'b0_101_0_10_01; // 3: (A * 10 + B * 4 + C * 2) >> 4
  localparam BLEND4 = 9'b0_110_0_01_01; // 4: (A * 12 + B * 2 + C * 2) >> 4
  localparam BLEND5 = 9'b0_010_0_11_11; // 5: (A * 4 + (B + C) * 6) >> 4
  localparam BLEND6 = 9'b0_111_1_xx_xx; // 6: (A * 14 + B + C) >> 4
  localparam AB = 2'b00;
  localparam AD = 2'b01;
  localparam DB = 2'b10;
  localparam BD = 2'b11;
  wire is_diff;
  DiffCheck diff_checker(rule[1] ? B : H,
                         rule[0] ? D : F,
                         is_diff);
  always @* begin
    case({!is_diff, rule[5:2]})
    1,17:  {op, input_ctrl} = {BLEND1, AB};
    2,18:  {op, input_ctrl} = {BLEND1, DB};
    3,19:  {op, input_ctrl} = {BLEND1, BD};
    4,20:  {op, input_ctrl} = {BLEND2, DB};
    5,21:  {op, input_ctrl} = {BLEND2, AB};
    6,22:  {op, input_ctrl} = {BLEND2, AD};

    8: {op, input_ctrl} = {BLEND0, 2'bxx};
    9: {op, input_ctrl} = {BLEND0, 2'bxx};
    10: {op, input_ctrl} = {BLEND0, 2'bxx};
    11: {op, input_ctrl} = {BLEND1, AB};
    12: {op, input_ctrl} = {BLEND1, AB};
    13: {op, input_ctrl} = {BLEND1, AB};
    14: {op, input_ctrl} = {BLEND1, DB};
    15: {op, input_ctrl} = {BLEND1, BD};

    24: {op, input_ctrl} = {BLEND2, DB};
    25: {op, input_ctrl} = {BLEND5, DB};
    26: {op, input_ctrl} = {BLEND6, DB};
    27: {op, input_ctrl} = {BLEND2, DB};
    28: {op, input_ctrl} = {BLEND4, DB};
    29: {op, input_ctrl} = {BLEND5, DB};
    30: {op, input_ctrl} = {BLEND3, BD};
    31: {op, input_ctrl} = {BLEND3, DB};
    default: {op, input_ctrl} = 11'bx;
    endcase
    
    // Setting op[8] effectively disables HQ2X because blend will always return E.
    if (disable_hq2x)
      op[8] = 1;
  end
  // Generate inputs to the inner blender. Valid combinations.
  // 00: E A B
  // 01: E A D 
  // 10: E D B
  // 11: E B D
  wire [14:0] Input1 = E;
  wire [14:0] Input2 = !input_ctrl[1] ? A :
                       !input_ctrl[0] ? D : B;
  wire [14:0] Input3 = !input_ctrl[0] ? B : D;
  InnerBlend inner_blend1(op, Input1[4:0],   Input2[4:0],   Input3[4:0],   Result[4:0]);
  InnerBlend inner_blend2(op, Input1[9:5],   Input2[9:5],   Input3[9:5],   Result[9:5]);
  InnerBlend inner_blend3(op, Input1[14:10], Input2[14:10], Input3[14:10], Result[14:10]);
endmodule

module Hq2x(input clk,
            input [14:0] inputpixel,
            input disable_hq2x,
            input reset_frame,
            input reset_line,
            input [9:0] read_x,
            output frame_available,
            output reg [14:0] outpixel);
reg [5:0] hqTable[0:255];
initial begin
hqTable[0] = 19; hqTable[1] = 19; hqTable[2] = 26; hqTable[3] = 11;
hqTable[4] = 19; hqTable[5] = 19; hqTable[6] = 26; hqTable[7] = 11;
hqTable[8] = 23; hqTable[9] = 15; hqTable[10] = 47; hqTable[11] = 35;
hqTable[12] = 23; hqTable[13] = 15; hqTable[14] = 55; hqTable[15] = 39;
hqTable[16] = 19; hqTable[17] = 19; hqTable[18] = 26; hqTable[19] = 58;
hqTable[20] = 19; hqTable[21] = 19; hqTable[22] = 26; hqTable[23] = 58;
hqTable[24] = 23; hqTable[25] = 15; hqTable[26] = 35; hqTable[27] = 35;
hqTable[28] = 23; hqTable[29] = 15; hqTable[30] = 7; hqTable[31] = 35;
hqTable[32] = 19; hqTable[33] = 19; hqTable[34] = 26; hqTable[35] = 11;
hqTable[36] = 19; hqTable[37] = 19; hqTable[38] = 26; hqTable[39] = 11;
hqTable[40] = 23; hqTable[41] = 15; hqTable[42] = 55; hqTable[43] = 39;
hqTable[44] = 23; hqTable[45] = 15; hqTable[46] = 51; hqTable[47] = 43;
hqTable[48] = 19; hqTable[49] = 19; hqTable[50] = 26; hqTable[51] = 58;
hqTable[52] = 19; hqTable[53] = 19; hqTable[54] = 26; hqTable[55] = 58;
hqTable[56] = 23; hqTable[57] = 15; hqTable[58] = 51; hqTable[59] = 35;
hqTable[60] = 23; hqTable[61] = 15; hqTable[62] = 7; hqTable[63] = 43;
hqTable[64] = 19; hqTable[65] = 19; hqTable[66] = 26; hqTable[67] = 11;
hqTable[68] = 19; hqTable[69] = 19; hqTable[70] = 26; hqTable[71] = 11;
hqTable[72] = 23; hqTable[73] = 61; hqTable[74] = 35; hqTable[75] = 35;
hqTable[76] = 23; hqTable[77] = 61; hqTable[78] = 51; hqTable[79] = 35;
hqTable[80] = 19; hqTable[81] = 19; hqTable[82] = 26; hqTable[83] = 11;
hqTable[84] = 19; hqTable[85] = 19; hqTable[86] = 26; hqTable[87] = 11;
hqTable[88] = 23; hqTable[89] = 15; hqTable[90] = 51; hqTable[91] = 35;
hqTable[92] = 23; hqTable[93] = 15; hqTable[94] = 51; hqTable[95] = 35;
hqTable[96] = 19; hqTable[97] = 19; hqTable[98] = 26; hqTable[99] = 11;
hqTable[100] = 19; hqTable[101] = 19; hqTable[102] = 26; hqTable[103] = 11;
hqTable[104] = 23; hqTable[105] = 61; hqTable[106] = 7; hqTable[107] = 35;
hqTable[108] = 23; hqTable[109] = 61; hqTable[110] = 7; hqTable[111] = 43;
hqTable[112] = 19; hqTable[113] = 19; hqTable[114] = 26; hqTable[115] = 11;
hqTable[116] = 19; hqTable[117] = 19; hqTable[118] = 26; hqTable[119] = 58;
hqTable[120] = 23; hqTable[121] = 15; hqTable[122] = 51; hqTable[123] = 35;
hqTable[124] = 23; hqTable[125] = 61; hqTable[126] = 7; hqTable[127] = 43;
hqTable[128] = 19; hqTable[129] = 19; hqTable[130] = 26; hqTable[131] = 11;
hqTable[132] = 19; hqTable[133] = 19; hqTable[134] = 26; hqTable[135] = 11;
hqTable[136] = 23; hqTable[137] = 15; hqTable[138] = 47; hqTable[139] = 35;
hqTable[140] = 23; hqTable[141] = 15; hqTable[142] = 55; hqTable[143] = 39;
hqTable[144] = 19; hqTable[145] = 19; hqTable[146] = 26; hqTable[147] = 11;
hqTable[148] = 19; hqTable[149] = 19; hqTable[150] = 26; hqTable[151] = 11;
hqTable[152] = 23; hqTable[153] = 15; hqTable[154] = 51; hqTable[155] = 35;
hqTable[156] = 23; hqTable[157] = 15; hqTable[158] = 51; hqTable[159] = 35;
hqTable[160] = 19; hqTable[161] = 19; hqTable[162] = 26; hqTable[163] = 11;
hqTable[164] = 19; hqTable[165] = 19; hqTable[166] = 26; hqTable[167] = 11;
hqTable[168] = 23; hqTable[169] = 15; hqTable[170] = 55; hqTable[171] = 39;
hqTable[172] = 23; hqTable[173] = 15; hqTable[174] = 51; hqTable[175] = 43;
hqTable[176] = 19; hqTable[177] = 19; hqTable[178] = 26; hqTable[179] = 11;
hqTable[180] = 19; hqTable[181] = 19; hqTable[182] = 26; hqTable[183] = 11;
hqTable[184] = 23; hqTable[185] = 15; hqTable[186] = 51; hqTable[187] = 39;
hqTable[188] = 23; hqTable[189] = 15; hqTable[190] = 7; hqTable[191] = 43;
hqTable[192] = 19; hqTable[193] = 19; hqTable[194] = 26; hqTable[195] = 11;
hqTable[196] = 19; hqTable[197] = 19; hqTable[198] = 26; hqTable[199] = 11;
hqTable[200] = 23; hqTable[201] = 15; hqTable[202] = 51; hqTable[203] = 35;
hqTable[204] = 23; hqTable[205] = 15; hqTable[206] = 51; hqTable[207] = 39;
hqTable[208] = 19; hqTable[209] = 19; hqTable[210] = 26; hqTable[211] = 11;
hqTable[212] = 19; hqTable[213] = 19; hqTable[214] = 26; hqTable[215] = 11;
hqTable[216] = 23; hqTable[217] = 15; hqTable[218] = 51; hqTable[219] = 35;
hqTable[220] = 23; hqTable[221] = 15; hqTable[222] = 7; hqTable[223] = 35;
hqTable[224] = 19; hqTable[225] = 19; hqTable[226] = 26; hqTable[227] = 11;
hqTable[228] = 19; hqTable[229] = 19; hqTable[230] = 26; hqTable[231] = 11;
hqTable[232] = 23; hqTable[233] = 15; hqTable[234] = 51; hqTable[235] = 35;
hqTable[236] = 23; hqTable[237] = 15; hqTable[238] = 7; hqTable[239] = 43;
hqTable[240] = 19; hqTable[241] = 19; hqTable[242] = 26; hqTable[243] = 11;
hqTable[244] = 19; hqTable[245] = 19; hqTable[246] = 26; hqTable[247] = 11;
hqTable[248] = 23; hqTable[249] = 15; hqTable[250] = 7; hqTable[251] = 35;
hqTable[252] = 23; hqTable[253] = 15; hqTable[254] = 7; hqTable[255] = 43;
end

reg [14:0] Prev0, Prev1, Prev2, Curr0, Curr1, Curr2, Next0, Next1, Next2;
reg [14:0] A, B, D, F, G, H;
reg [7:0] pattern, nextpatt;
reg [1:0] i;
reg [7:0] y;
reg [1:0] yshort; // counts only lines 0-3, then stays on 3.
reg [8:0] offs;
reg first_pixel;
reg [14:0] inbuf[0:511];   // 2 lines of input pixels
reg [14:0] outbuf[0:2047]; // 4 lines of output pixels


wire curbuf = y[0];
reg last_line;
wire prevbuf = (yshort <= 1) ? curbuf : !curbuf;
wire writebuf = !curbuf;
reg writestep;

wire diff0, diff1;
DiffCheck diffcheck0(Curr1, (i == 0) ? Prev0 : (i == 1) ? Curr0 : (i == 2) ? Prev2 : Next1, diff0);
DiffCheck diffcheck1(Curr1, (i == 0) ? Prev1 : (i == 1) ? Next0 : (i == 2) ? Curr2 : Next2, diff1);
wire [7:0] new_pattern = {diff1, diff0, pattern[7:2]};
always @(posedge clk)
  pattern <= new_pattern;

wire less_254 = (offs >= 510) || (offs < 254);
wire [8:0] inbuf_rd_addr = {i[0] == 0 ? prevbuf : curbuf, offs[7:0]};

always @(posedge clk) begin
  if (i == 0 && less_254) Curr2 <= inbuf[inbuf_rd_addr];
  if (i == 1 && less_254) begin
    Prev2 <= Curr2;
    Curr2 <= inbuf[inbuf_rd_addr];
  end
  if (i == 2 && less_254) begin
    Next2 <= last_line ? Curr2 : inputpixel;
    inbuf[{writebuf, offs[7:0]}] <= inputpixel;
  end
end

wire [14:0] X = (i == 0) ? A : (i == 1) ? Prev1 : (i == 2) ? Next1 : G;
wire [14:0] blend_result;
Blend blender(hqTable[nextpatt], disable_hq2x, Curr0, X, B, D, F, H, blend_result);

always @(posedge clk) begin
  if (!offs[8])
    outbuf[{curbuf, i[1], offs[7:0], i[1]^i[0]}] <= blend_result;
  if (!writestep) begin
    nextpatt <= {nextpatt[5], nextpatt[3], nextpatt[0], nextpatt[6], nextpatt[1], nextpatt[7], nextpatt[4], nextpatt[2]};
    {B, F, H, D} <= {F, H, D, B};
  end else begin
    nextpatt <= {new_pattern[7:6], new_pattern[3], new_pattern[5], new_pattern[2], new_pattern[4], new_pattern[1:0]};
    {A, G} <= {Prev0, Next0};
    {B, F, H, D} <= {Prev1, Curr2, Next1, Curr0};
    {Prev0, Prev1} <= {first_pixel ? Prev2 : Prev1, Prev2};
    {Curr0, Curr1} <= {first_pixel ? Curr2 : Curr1, Curr2};
    {Next0, Next1} <= {first_pixel ? Next2 : Next1, Next2};
  end
end

reg last_reset_line;
initial last_reset_line = 0;

always @(posedge clk) begin
  outpixel <= outbuf[{!curbuf, read_x}];
  if (writestep) begin
    offs <= offs + 9'b1;
    first_pixel <= 0;
  end
  i <= i + 2'b1;
  writestep <= (i == 2);
  if (reset_line) begin
    offs <= -2;
    first_pixel <= 1;
    i <= 0;
    writestep <= 0;
    // Increment Y only once.
    if (!last_reset_line) begin
      y <= y + 8'b1;
      yshort <= (yshort == 3) ? yshort : (yshort + 2'b1);
      last_line <= ((y + 8'b1) >= 240);
    end
    
    
  end
  if (reset_frame) begin
    y <= 0;
    yshort <= 0;
    last_line <= 0;
  end
  last_reset_line <= reset_line;
end
assign frame_available = (i == 0) && first_pixel && (yshort == 2) && !reset_line;
endmodule  // Hq2x
// Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.

module video(
	input  clk,
	input [5:0] color,
	input [8:0] count_h,
	input [8:0] count_v,
	input mode,
	input ypbpr,
	input smoothing,
	input scanlines,
	input overscan,
	input palette,
	

	output       VGA_HS,
	output       VGA_VS,
	output [3:0] VGA_R,
	output [3:0] VGA_G,
	output [3:0] VGA_B,
	
	output osd_visible
);

reg clk2 = 1'b0;
always @(posedge clk) clk2 <= ~clk2;
wire clkv = mode ? clk2 : clk;

wire [5:0] R_out, G_out, B_out;



// NTSC UnsaturatedV6 palette
//see: http://www.firebrandx.com/nespalette.html
/*reg [15:0] pal_unsat_lut[0:63];
initial $readmemh("nes_palette_unsaturatedv6.txt", pal_unsat_lut);*/

// FCEUX palette
reg [15:0] pal_fcelut[0:63];
initial $readmemh("design03-data1.hex", pal_fcelut);

wire [14:0] pixel = pal_fcelut[color][14:0];
 
// Horizontal and vertical counters
reg [9:0] h, v;
wire hpicture  = (h < 512);             // 512 lines of picture
wire hend = (h == 681);                 // End of line, 682 pixels.
wire vpicture = (v < (480 >> mode));    // 480 lines of picture
wire vend = (v == (523 >> mode));       // End of picture, 524 lines. (Should really be 525 according to NTSC spec)

wire [14:0] doubler_pixel;
wire doubler_sync;

scan_double doubler(clk, pixel,
		            count_v[8],                 // reset_frame
		            (count_h[8:3] == 42),       // reset_line
		            {v[0], h[9] ? 9'd0 : h[8:0] + 9'd1}, // 0-511 for line 1, or 512-1023 for line 2.
		            doubler_pixel);             // pixel is outputted


reg [8:0] old_count_v;
wire sync_frame = (old_count_v == 9'd511) && (count_v == 9'd0);

assign doubler_sync = sync_frame;

always @(posedge clkv) begin
  h <= (hend || (mode ? sync_frame : doubler_sync)) ? 10'd0 : h + 10'd1;
  if(mode ? sync_frame : doubler_sync) v <= 0;
    else if (hend) v <= vend ? 10'd0 : v + 10'd1;

  old_count_v <= count_v;
end

wire [14:0] pixel_v = (!hpicture || !vpicture) ? 15'd0 : mode ? pixel : doubler_pixel;
wire darker = !mode && v[0] && scanlines;

// display overlay to hide overscan area
// based on Mario3, DoubleDragon2, Shadow of the Ninja
wire ol = overscan && ( (h > 512-16) || 
								(h < 20) || 
								(v < (mode ? 6 : 12)) || 
								(v > (mode ? 240-10 : 480-20)) 
							  );

wire  [4:0]   vga_r = ol ? {4'b0, pixel_v[4:4]}   : (darker ? {1'b0, pixel_v[4:1]} : pixel_v[4:0]);
wire  [4:0]   vga_g = ol ? {4'b0, pixel_v[9:9]}   : (darker ? {1'b0, pixel_v[9:6]} : pixel_v[9:5]);
wire  [4:0]   vga_b = ol ? {4'b0, pixel_v[14:14]} : (darker ? {1'b0, pixel_v[14:11]} : pixel_v[14:10]);
wire         sync_h = ((h >= (512 + 23 + (mode ? 18 : 35))) && (h < (512 + 23 + (mode ? 18 : 35) + 82)));
wire         sync_v = ((v >= (mode ? 240 + 5  : 480 + 10))  && (v < (mode ? 240 + 14 : 480 + 12)));


assign VGA_HS = !sync_h;
assign VGA_VS = !sync_v;
assign VGA_R = vga_r[4:1];
assign VGA_G = vga_g[4:1];
assign VGA_B = vga_b[4:1];

endmodule
/*
The virtual NES cartridge
At the moment this stores the entire cartridge
in SPRAM, in the future it could stream data from
SQI flash, which is more than fast enough
*/

module cart_mem(
  input clock,
  input reset,
  
  input reload,
  input [3:0] index,
  
  output cart_ready,
  output reg [31:0] flags_out,
  //address into a given section - 0 is the start of CHR and PRG,
  //region is selected using the select lines for maximum flexibility
  //in partitioning
  input [20:0] address,
  
  input prg_sel, chr_sel,
  input ram_sel, //for cart SRAM (NYI)
  
  input rden, wren,
  
  input  [7:0] write_data,
  output [7:0] read_data,
  
  //Flash load interface
  output flash_csn,
  output flash_sck,
  output flash_mosi,
  input flash_miso
);

reg load_done;
initial load_done = 1'b0;

wire cart_ready = load_done;
// Does the image use CHR RAM instead of ROM? (i.e. UNROM or some MMC1)
wire is_chram = flags_out[15];
// Work out whether we're in the SPRAM, used for the main ROM, or the extra 8k SRAM
wire spram_en = prg_sel | (!is_chram && chr_sel);
wire sram_en = ram_sel | (is_chram && chr_sel);

wire [16:0] decoded_address;
assign decoded_address = chr_sel ? {1'b1, address[15:0]} : address[16:0];

reg [15:0] load_addr;
wire [14:0] spram_address = load_done ? decoded_address[16:2] : load_addr[14:0];

wire load_wren;
wire spram_wren = load_done ? (spram_en && wren) : load_wren;
wire [3:0] spram_mask = load_done ? (4'b0001 << decoded_address[1:0]) : 4'b1111;
wire [3:0] spram_maskwren = spram_wren ? spram_mask : 4'b0000;

wire [31:0] load_write_data;
wire [31:0] spram_write_data = load_done ? {write_data, write_data, write_data, write_data} : load_write_data;

wire [31:0] spram_read_data;

wire [7:0] csram_read_data;
// Demux the 32-bit memory
assign read_data = sram_en ? csram_read_data : 
    (decoded_address[1] ? (decoded_address[0] ? spram_read_data[31:24] : spram_read_data[23:16]) : (decoded_address[0] ? spram_read_data[15:8] : spram_read_data[7:0]));

 // The SRAM, used either for PROG_SRAM or CHR_SRAM
generic_ram #(
  .WIDTH(8),
  .WORDS(8192)
) sram_i (
  .clock(clock),
  .reset(reset),
  .address(decoded_address[12:0]), 
  .wren(wren&sram_en), 
  .write_data(write_data), 
  .read_data(csram_read_data)
);
// The SPRAM (with a generic option), which stores
// the ROM
`ifdef no_spram_prim
  reg [31:0] spram_mem[0:32767];
  reg [31:0] spram_dout_pre;
  always @(posedge clock)
  begin
    spram_dout_pre <= spram_mem[spram_address];
    if(spram_maskwren[0]) spram_mem[spram_address] <= spram_write_data[7:0];
    if(spram_maskwren[1]) spram_mem[spram_address] <= spram_write_data[15:8];
    if(spram_maskwren[2]) spram_mem[spram_address] <= spram_write_data[23:16];
    if(spram_maskwren[3]) spram_mem[spram_address] <= spram_write_data[31:24];
  end;
  assign spram_read_data <= spram_dout_pre;
`else

  reg [14:0] address_reg;
  reg [3:0] wen_reg;
  reg [31:0] data_reg;
  always @(posedge clock)
  begin
    address_reg <= spram_address;
    wen_reg <= spram_maskwren;
    data_reg <= spram_write_data;
  end
  up_spram spram_i (
    .clk(clock),
    .wen(wen_reg),
    .addr(address_reg),
    .wdata(data_reg),
    .rdata(spram_read_data)
  );
`endif


wire flashmem_valid = !load_done;
wire flashmem_ready;
assign load_wren =  flashmem_ready && (load_addr != 16'h8000);
wire [23:0] flashmem_addr = (24'h100000 + (index_lat << 18)) | {load_addr, 2'b00};
reg [3:0] index_lat;
reg load_done_pre;

reg [7:0] wait_ctr;
// Flash memory load interface
always @(posedge clock) 
begin
  if (reset == 1'b1) begin
    load_done_pre <= 1'b0;
    load_done <= 1'b0;
    load_addr <= 16'h0000;
    flags_out <= 32'h00000000;
    wait_ctr <= 8'h00;
    index_lat <= 4'h0;
  end else begin
    if (reload == 1'b1) begin
      load_done_pre <= 1'b0;
      load_done <= 1'b0;
      load_addr <= 16'h0000;
      flags_out <= 32'h00000000;
      wait_ctr <= 8'h00;
      index_lat <= index;
    end else begin
      if(!load_done_pre) begin
        if (flashmem_ready == 1'b1) begin
          if (load_addr == 16'h8000) begin
            load_done_pre <= 1'b1;
            flags_out <= load_write_data; //last word is mapper flags
          end else begin
            load_addr <= load_addr + 1'b1;
          end;
        end
      end else begin
        if (wait_ctr < 8'hFF)
          wait_ctr <= wait_ctr + 1;
        else
          load_done <= 1'b1;
      end
      
    end
  end
end



icosoc_flashmem flash_i (
	.clk(clock),
  .reset(reset),
  .valid(flashmem_valid),
  .ready(flashmem_ready),
  .addr(flashmem_addr),
  .rdata(load_write_data),

	.spi_cs(flash_csn),
	.spi_sclk(flash_sck),
	.spi_mosi(flash_mosi),
	.spi_miso(flash_miso)
);

endmodule
