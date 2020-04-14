module FSM1 (Clk, Reset, SlowRam, Read, Write);
input Clk, Reset, SlowRam;
output Read, Write;

reg Read, Write, Wait, Delay;

parameter [3:0] ST_Read = 0, ST_Write = 1, ST_Delay = 2,
                ST_Trx = 3, ST_Hold = 4, ST_Block = 5,
                ST_Wait = 6, ST_Turn = 7, ST_Quit = 8,
                ST_Exit = 9, ST_Done = 10;
reg       [3:0] CurState, NextState;


always @(posedge Clk) begin:SEQ
  if (Reset)
    CurState = ST_Read;
  else
    CurState = NextState;
end

initial begin
  Read = 0;
  Write = 1;
  Wait = 0;
  Delay = 1;
end

always @(CurState) begin:COMB
  case (CurState)

    ST_Trx: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Read == 1) NextState = ST_Hold;
      else if (Write == 1) NextState = ST_Block;
      else if (SlowRam == 1) NextState = ST_Wait;
      else if (Wait == 0) NextState = ST_Turn;
      else if (Delay == 1) NextState = ST_Quit;
      else NextState = ST_Block;
    end

    ST_Hold: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Read == 0) NextState = ST_Hold;
      else if (Write == 0) NextState = ST_Block;
      else if (SlowRam == 0) NextState = ST_Wait;
      else if (Wait == 1) NextState = ST_Turn;
      else if (Delay == 0) NextState = ST_Quit;
      else NextState = ST_Block;
    end

    ST_Block: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Read == 1) NextState = ST_Wait;
      else if (Write == 1) NextState = ST_Turn;
      else if (SlowRam == 1) NextState = ST_Quit;
      else if (Wait == 0) NextState = ST_Done;
      else if (Delay == 1) NextState = ST_Exit;
      else NextState = ST_Block;
    end

    ST_Wait: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Delay == 1) NextState = ST_Quit;
      else if (Wait == 0) NextState = ST_Read;
      else NextState = ST_Turn;
    end

    ST_Turn: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Delay == 0) NextState = ST_Write;
      else if (Wait == 0) NextState = ST_Read;
      else NextState = ST_Exit;
    end

    ST_Quit: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Wait == 1) NextState = ST_Wait;
      else if (Write == 0) NextState = ST_Read;
      else NextState = ST_Turn;
    end

    ST_Exit: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Delay == 1) NextState = ST_Done;
      else if (Wait == 0) NextState = ST_Read;
      else NextState = ST_Write;
    end

    ST_Done: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = ~Write;
      Write = ~Read;
      if (Delay == 1) NextState = ST_Quit;
      else if (Wait == 0) NextState = ST_Read;
      else NextState = ST_Turn;
    end

    ST_Read: begin
      Read = 1;
      Write = 0;
      Wait = ~Wait;
      Delay = ~Delay;
      NextState = ST_Write;
    end
    
    ST_Write: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = 0;
      Write = 1;
      if (SlowRam)
        NextState = ST_Delay;
      else
        NextState = ST_Read;
    end
    
    ST_Delay: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = 0;
      Write = 0;
      NextState = ST_Read;
    end
    
    default: begin
      Wait = ~Wait;
      Delay = ~Delay;
      Read = 0;
      Write = 0;
      NextState = ST_Read;
    end
    
  endcase
end

endmodule


