/*
 * Derived from PR#513
 */

`timescale 1 ps / 1 ps

module example;
    integer fd;

    initial begin
    #100
    fd = $fopen( "example.dump" );
    $fdisplay( fd );
    #1000
    $display( "PASSED" );
    end
endmodule
