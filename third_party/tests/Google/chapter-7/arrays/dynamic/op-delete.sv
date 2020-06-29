/*
:name: dynamic-arrays-op-delete
:description: Test dynamic arrays operator delete support
:tags: 7.5.3
:type: simulation parsing
*/
module top ();

bit [7:0] arr[];

initial begin
    arr = new [ 16 ];
    $display(":assert: (%d == 16)", arr.size);
    arr.delete;
    $display(":assert: (%d == 0)", arr.size);
end

endmodule
