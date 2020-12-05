package pkg1;
    typedef struct packed {
        logic [7:0] first;
    } struct1;
endpackage

package pkg2;
    typedef struct packed {
        logic [6:0] second;
    } struct1;
endpackage

module dut(var1, var2, var3);
    typedef struct packed {
        logic [5:0] third;
    } struct2;

    output pkg1::struct1 var1;
    output pkg2::struct1 var2;
    output struct2 var3;

    assign var1.first = 255;
    assign var2.second = 127;
    assign var3.third = 63;
endmodule;
