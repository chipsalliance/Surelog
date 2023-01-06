`default_nettype none

module top;
    function integer doFoo(input integer depth);
        doFoo = $clog2($bits(depth));
    endfunction
endmodule // top
