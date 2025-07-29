
`define BOARD [8:0]

module FindMoveMask (
    Blk,
    Wht,
    Moves
);

input  `BOARD Blk;
input  `BOARD Wht;
output `BOARD Moves;

// moves only allowed to empty squares
wire `BOARD Emp = ~(Blk | Wht);

// Masks of moves considering the state in each of the 8 possible directions
wire `BOARD Move_N;
wire `BOARD Move_E;
wire `BOARD Move_W;
wire `BOARD Move_S;

// Combine all moves
wire `BOARD Moves = Move_N | Move_E | Move_W | Move_S ;

// Create all moves
assign Move_N  [00] = 1'b0;
assign Move_N  [01] = 1'b0;
assign Move_N  [02] = 1'b0;
assign Move_N  [03] = 1'b0;
assign Move_N  [04] = 1'b0;
assign Move_N  [05] = 1'b0;
assign Move_N  [06] = Emp[06] && Wht[03] && Blk[00];
assign Move_N  [07] = Emp[07] && Wht[04] && Blk[01];
assign Move_N  [08] = Emp[08] && Wht[05] && Blk[02];

assign Move_E  [00] = 1'b0;
assign Move_E  [01] = 1'b0;
assign Move_E  [02] = Emp[02] && Wht[01] && Blk[00];
assign Move_E  [03] = 1'b0;
assign Move_E  [04] = 1'b0;
assign Move_E  [05] = Emp[05] && Wht[04] && Blk[03];
assign Move_E  [06] = 1'b0;
assign Move_E  [07] = 1'b0;
assign Move_E  [08] = Emp[08] && Wht[07] && Blk[06];

assign Move_W  [00] = Emp[00] && Wht[01] && Blk[02];
assign Move_W  [01] = 1'b0;
assign Move_W  [02] = 1'b0;
assign Move_W  [03] = Emp[03] && Wht[04] && Blk[05];
assign Move_W  [04] = 1'b0;
assign Move_W  [05] = 1'b0;
assign Move_W  [06] = Emp[06] && Wht[07] && Blk[08];
assign Move_W  [07] = 1'b0;
assign Move_W  [08] = 1'b0;

assign Move_S  [00] = Emp[00] && Wht[03] && Blk[06];
assign Move_S  [01] = Emp[01] && Wht[04] && Blk[07];
assign Move_S  [02] = Emp[02] && Wht[05] && Blk[08];
assign Move_S  [03] = 1'b0;
assign Move_S  [04] = 1'b0;
assign Move_S  [05] = 1'b0;
assign Move_S  [06] = 1'b0;
assign Move_S  [07] = 1'b0;
assign Move_S  [08] = 1'b0;

endmodule
