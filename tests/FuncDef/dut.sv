module mulAddRecFNToRaw_preMul ();

function integer clog2;
    input integer a;

    begin
        a = a - 1;
        for (clog2 = 0; a > 0; clog2 = clog2 + 1) a = a>>1;
    end

endfunction
   
    countLeadingZeros#(clog2(prodWidth + 4) - 1)
        countLeadingZeros_notCDom(
            notCDom_reduced2AbsSigSum, notCDom_normDistReduced2);
endmodule
