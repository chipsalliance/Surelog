
// To create a GIF animation from the generated images:
// convert frame_*.ppm pong.gif

`undef WRITE_FRAMES_PPM
`define MAX_NUMBER_FRAMES 3

module testbench;

reg clk, reset;
reg [1:0] btn1;
reg [1:0] btn2;
wire hsync, vsync;
wire [2:0] rgb;

top UUT (
	clk,
	reset,
	btn1,
	btn2,
	hsync,
	vsync,
	rgb
);

initial begin
	clk <= 0;
	#100;
	forever begin
		clk <= ~clk;
		#50;
	end
end

initial begin
	btn1 <= 2'b00;
	btn2 <= 2'b00;
	reset <= 1;
	repeat(5) @(posedge clk);
	btn2 <= 2'b01;
	repeat(5) @(posedge clk);
	reset <= 0;
end

integer x, y, z, idx, fd;
reg [128*8-1:0] filename;
reg [2:0] framebuffer [0:700*500-1];
reg last_hsync, last_vsync;
reg [63:0] hash;

always @(posedge clk) begin
	last_hsync <= hsync;
	last_vsync <= vsync;
	if (reset) begin
		x = 96;
		y = 12;
		z = 0;
		for (idx = 0; idx < 700*500; idx=idx+1)
			framebuffer[idx] = 0;
	end else
	if (hsync) begin
		if (!last_hsync) begin
			x = 0;
			y = y + 1;
			if (z == 0 && y == 13)
				$write("Frame %3d .", z);
			if (z != 0 && y == 1)
				$write("Frame %3d ", z);
			if (y % 10 == 9) begin
				$write(".");
				$fflush;
			end
		end
	end else
	if (vsync) begin
		if (!last_vsync)
		begin
			hash = 0;
			for (idx=0; idx < 700*500; idx = idx+1)
				hash = framebuffer[idx] + (hash << 6) + (hash << 16) - hash;
			$write(" %016x", hash);

`ifdef WRITE_FRAMES_PPM
			$swrite(filename, "frame_%03d.ppm", z);
			$write(" [%-0s]", filename);
			fd = $fopen(filename, "w");

			$fwrite(fd, "P3\n");
			$fwrite(fd, "# pong frame\n");
			$fwrite(fd, "700 500\n");
			$fwrite(fd, "1\n");
			for (idx=0; idx < 700*500; idx = idx+1)
				$fwrite(fd, "%b %b %b\n", framebuffer[idx][0], framebuffer[idx][1], framebuffer[idx][2]);
			$fclose(fd);
`endif

			$write("\n");

			x = 0;
			y = 0;
			z = z + 1;
			for (idx = 0; idx < 700*500; idx=idx+1)
				framebuffer[idx] = 0;

			if (z == `MAX_NUMBER_FRAMES)
				$finish;
		end
	end else begin
		x <= x + 1;
		if (x % 2 == 0 && 5 <= x && x < 1405 && 5 <= y && y < 505) begin
			idx = (x-5)/2 + 700*(y-5);
			framebuffer[idx] = rgb;
		end
	end
end

initial begin
	// $dumpfile("bench.vcd");
	// $dumpvars(0, testbench);
end

endmodule
