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

module dut (a, o);
    input [3:0] a;
    output [2:0] o;
    wire [3:0] a;
    reg [2:0] o;
  assign o = a[3:1];
endmodule
