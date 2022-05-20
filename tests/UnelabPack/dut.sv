package pkg1;
localparam X = 4;
endpackage

package pkg2;
localparam Y = pkg1::X;
endpackage
