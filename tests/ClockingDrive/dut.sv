

module main;


default clocking cb @(posedge clk); // Assume clk has a period of #10 units
output v;
endclocking
initial begin
#3 cb.v <= expr1; // Matures in cycle 1; equivalent to ##1 cb.v <= expr1
end
initial begin
    cb.a <= c; // The value of a will change in the Re-NBA region
    cb.b <= cb.a; // b is assigned the value of a before the change


    bus.data[3:0] <= 4'h5; // drive data in Re-NBA region of the current cycle
    ##1 bus.data <= 8'hz; // wait 1 default clocking cycle, then drive data
    ##2; bus.data <= 2; // wait 2 default clocking cycles, then drive data
    bus.data <= ##2 r; // remember the value of r and then drive
    // data 2 (bus) cycles later
    bus.data <= #4 r; // error: regular intra-assignment delay not allowed
    // in synchronous drives
    ##1; // Wait until cycle 1
    cb.v <= expr1; // Matures in cycle 1, v is assigned expr1
    cb.v <= ##2 expr2; // Matures in cycle 3
    #1 cb.v <= ##2 expr3; // Matures in cycle 3
    ## 1;
cb.a <= 1'b0;
@(x); // x is triggered by reactive stimulus running in same time step
cb.a <= 1'b1;
##2;
pe.nibble <= 4'b0101;
pe.nibble <= 4'b0011;
    end
endmodule
