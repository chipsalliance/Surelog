module vga_sync
   (
    input wire clk, reset,
    output wire hsync, vsync, video_on, p_tick,
    output wire [9:0] pixel_x, pixel_y
   );

   localparam HD = 640; // horizontal display area
   localparam HF = 48 ; // h. front (left) border
   localparam HB = 16 ; // h. back (right) border
   localparam HR = 96 ; // h. retrace
   localparam VD = 480; // vertical display area
   localparam VF = 10;  // v. front (top) border
   localparam VB = 33;  // v. back (bottom) border
   localparam VR = 2;   // v. retrace

   reg point;
   wire point_next;
   reg [9:0] h_count, h_count_next;
   reg [9:0] v_count, v_count_next;
   reg v_sync_reg, h_sync_reg;
   wire v_sync_next, h_sync_next;
   wire h_end, v_end, pixel_tick;

   
   always @(posedge clk, posedge reset)
      if (reset)
         begin
            point <= 1'b0;
            v_count <= 0;
            h_count <= 0;
            v_sync_reg <= 1'b0;
            h_sync_reg <= 1'b0;
         end
      else
         begin
            point <= point_next;
            v_count <= v_count_next;
            h_count <= h_count_next;
            v_sync_reg <= v_sync_next;
            h_sync_reg <= h_sync_next;
         end

   assign point_next = ~point;
   assign pixel_tick = point;

   assign h_end = (h_count==(HD+HF+HB+HR-1));
   assign v_end = (v_count==(VD+VF+VB+VR-1));

   always @*
      if (pixel_tick)  // 25 MHz pulse
         if (h_end)
			begin

            h_count_next = 0;
				if(v_end)
					v_count_next = 0;
				else
					v_count_next = v_count + 1;
			end
         else begin
            h_count_next = h_count + 1;
	    v_count_next = v_count;
	 end
      else
		begin
         h_count_next = h_count;
			v_count_next = v_count;
		end

   assign h_sync_next = (h_count >=(HD+HB) &&
                         h_count <=(HD+HB+HR-1));
   assign v_sync_next = (v_count >=(VD+VB) &&
                         v_count <=(VD+VB+VR-1));

   assign video_on = (h_count<HD) && (v_count<VD);

   assign hsync = h_sync_reg;
   assign vsync = v_sync_reg;
   assign pixel_x = h_count;
   assign pixel_y = v_count;
   assign p_tick = pixel_tick;

endmodule
