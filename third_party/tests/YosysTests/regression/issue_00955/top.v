module shifttest ( addr, out );
    input [7:0] addr;
    output [7:0] out;
    assign out[0] = 256'haaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000 >> addr;
    assign out[1] = 256'h6666aaaacccc00006666aaaacccc00006666aaaacccc00006666aaaacccc0000 >> addr;
    assign out[2] = 256'h1e1e66665a5aaaaab4b4ccccf0f000001e1e66665a5aaaaab4b4ccccf0f00000 >> addr;
    assign out[3] = 256'h01fe1e1e39c666666d925a5a55aaaaaaab54b4b4936cccccc738f0f0ff000000 >> addr;
    assign out[4] = 256'h5554ab545294b4b44924936c66cccccc3398c7381c70f0f007c0ff0000000000 >> addr;
    assign out[5] = 256'h999833986318c7388e381c7078f0f0f0c3e007c01f80ff00f800000000000000 >> addr;
    assign out[6] = 256'he1e0c3e083e007c00fc01f807f00ff00fc00f800e00000000000000000000000 >> addr;
    assign out[7] = 256'hfe00fc00fc00f800f000e0008000000000000000000000000000000000000000 >> addr;
endmodule
