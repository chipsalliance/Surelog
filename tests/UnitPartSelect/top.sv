module toto();

  parameter IDLE = 0;

  reg [3:0] state, next;

  always @(posedge clk ) begin

    state[IDLE] <= 1'b1;

    if (InterruptStatus[0]==0) begin 
    end

    if (ConnectionState[3:0]!=ESTABLISHED) begin 
    end

  end

endmodule