
module constpower(ys, yu);

output [2:0] ys, yu;

genvar i, j;

generate
	for (i = 0; i < 2; i = i+1) 
	for (j = 0; j < 2; j = j+1) begin:W
		assign ys= i + j;
		
	end

endgenerate

endmodule

/*

interface rggen_register_if #(
);
 

  logic                     valid;
  logic [31:0]   value;

  modport register (
    input   valid,
    output  value
  );

  modport monitor (
    input valid,
    input value
  );
endinterface


module rggen_bit_field (input logic [31:0] o_value);
endmodule

module top();
  rggen_register_if  register_if[1]();


  // assign o = register_if[0].value[8+:1];
  
  rggen_bit_field i1 (
    .o_value            (register_if)
  );

   rggen_bit_field  u_bit_field (
    .o_value            (register_if[0].value[8+:1])
  );
  

endmodule

*/