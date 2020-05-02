program TESTBENCH #(parameter width = 1) (input wire [width-1:0] observe, output reg [width-1:0] drive);
  initial begin
    $dumpfile("test.vcd");
    $dumpvars;
    $monitor("@%0dns i = %0d, o = %0d",$time,drive, observe);
    drive = 3'b000;
    #1 assert(drive == observe) $display("OK!"); else $fatal(1, "drive != observe!");
    #5 drive = 3'b111;
    #1 assert(drive == observe) $display("OK!"); else $fatal(1, "drive != observe!");
    #100 $finish();

  end
endprogram


module TOP();
  parameter width = 16;
  wire [width-1:0] i;
  wire [width-1:0] o;
  ConnectTB #(width) conntb(.con_i(i),.con_o(o));
  dut #(width) dut1(.i(conntb.con_i), .o(conntb.con_o));
  TESTBENCH #(width) tb(.observe(conntb.con_o),.drive(conntb.con_i));
endmodule
