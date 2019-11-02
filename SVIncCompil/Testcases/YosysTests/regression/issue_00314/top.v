module top(a,b,z);
    parameter width_a = 8;
    parameter width_b = 8;
    input [width_a-1:0] a;
    input [width_b-1:0] b;
    output [width_a-1:0] z;
    reg  [width_a-1:0] z;

    always@(a or b)
    begin
        div_u(a,b,z);
    end

    function [width_b:0] minus;
        input [width_b:0] in1;
        input [width_b:0] in2;
        minus = in1 - in2;
    endfunction

    task divmod;
        input [width_a-1:0] l;
        input [width_b-1:0] r;
        output [width_a-1:0] rdiv;
        output [width_b-1:0] rmod;

        parameter llen = width_a;
        parameter rlen = width_b;
        reg [(llen+rlen)-1:0] lbuf;
        reg [rlen:0] diff;
        integer i;
        begin
            lbuf = 0;
            lbuf[llen-1:0] = l;
            for(i=width_a-1;i>=0;i=i-1)
            begin
                diff = minus(lbuf[(llen+rlen)-1:llen-1], {1'b0,r});
                rdiv[i] = ~diff[rlen];
                if(diff[rlen] == 0)
                    lbuf[(llen+rlen)-1:llen-1] = diff;
                lbuf[(llen+rlen)-1:1] = lbuf[(llen+rlen)-2:0];
            end
        rmod = lbuf[(llen+rlen)-1:llen];
        end
    endtask

    task div_u;
        input [width_a-1:0] l;
        input [width_b-1:0] r;
        output [width_a-1:0] rdiv;

        reg [width_a-01:0] rdiv;    // <-- this line causes problem
        reg [width_b-1:0] rmod;
        begin
            divmod(l, r, rdiv, rmod);
        end
    endtask

endmodule
