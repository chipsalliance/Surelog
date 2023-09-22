module AnonymousUnion(output int o);
   union packed {
      int v1;
      int v2;
   } un;

   initial begin
      un.v1 = 1;
      o = un.v2;
   end
endmodule

module AssignToUnionAndReadField(output logic [3:0] o);
   union packed {
      bit [3:0] field;
   } un;

   initial begin
      un = 4'hA;
      o = un.field;
   end
endmodule
