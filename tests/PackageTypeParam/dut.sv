package new_package;   
typedef struct packed {
    logic [128:0] a;
    logic [4:0]   b;
    logic         c;
    logic         d;
    logic         e;
} zzz;
endpackage : new_package;


module module_a
  #(
    parameter type TYPE_PARAMETER = new_package::zzz
    )
  (
   input TYPE_PARAMETER input_struct,
   output TYPE_PARAMETER output_struct,
   input clk

   );

  always_ff @(posedge clk) begin
    output_struct <= input_struct;
  end


endmodule : module_a
