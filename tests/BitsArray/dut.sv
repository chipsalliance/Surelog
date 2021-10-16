
module aes_reg_status #(
   parameter int Width = 1
)(
   input logic [Width-1:0] we_i
);
endmodule

module top;

   bit fcoe_reserved_before_sof[];

   logic [7:0] key_init_we [2];

   aes_reg_status #(
      .Width ( $bits(key_init_we) )
   ) u_reg_status_key_init (
      .we_i( {key_init_we[1], key_init_we[0]} )
   );
   
endmodule

module toto();

 bit fcoe_reserved_before_sof[];

 parameter   a = $bits(fcoe_reserved_before_sof[0]);


endmodule // toto

