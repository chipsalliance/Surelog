
interface r5p_bus_if ();
 
 logic          vld;  // valid
 
 modport  man (
   output vld
 );
 
endinterface: r5p_bus_if

module r5p_bus_dec #(
  int unsigned BN = 2    
)(
  r5p_bus_if.man m[BN-1:0]   
);

genvar i;

generate
for (i=0; i<BN; i++) begin: gen_loop
  // forward path
  assign m[i].vld = s_dec[i] ? 1 : '0;
  
end: gen_loop
endgenerate


endmodule
