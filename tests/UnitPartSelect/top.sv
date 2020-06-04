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


module dut_part_select(input [2:0] a, output [2:0] b);
  wire [2:0] a;
  reg [2:0] b;
  assign b[2] = a[0];
  assign b[1:0] = a[2:1];
endmodule


module dut_no_decl(input [2:0] a, output [2:0] b);
  assign b[2] = a[0];
  assign b[1:0] = a[2:1];
endmodule

