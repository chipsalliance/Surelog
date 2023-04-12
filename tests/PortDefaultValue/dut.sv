
module top();
bus_conn u1();
endmodule

module bus_conn (
input [7:0] datain = 8'hFF);
endmodule

/*
module bus_connect1 (
output logic [31:0] dataout,
input [ 7:0] datain);
parameter logic [7:0] My_DataIn = 8'h00;
bus_conn bconn0 (dataout[31:24], 8'h0F);
// Constant literal overrides default in bus_conn definition
bus_conn bconn1 (dataout[23:16]);
// Omitted port for datain, default parameter value 8'hFF in
// bus_conn used
bus_conn bconn2 (dataout[15:8], My_DataIn);
// The parameter value 8'h00 from the instantiating scope is used
bus_conn bconn3 (dataout[7:0]);
endmodule
*/


/*


module M2(input o1 = 1'b1);
endmodule

module M1(input o1);
 M2 u1();
  //M2 u2(o2);
endmodule
*/
/*
module top();
  M1 u1();
  M1 u2();
endmodule
*/
/*
interface interf();
  logic a;

endinterface

module top(input rd_impl_conn, rd_name_conn);
   interf intf();

   ibex_csr #(
   ) u_mie_csr (
     .rd_impl_conn(intf.ab)
   );
 
endmodule

module ibex_csr #(
 ) (
       input logic rd_const_conn,
       output logic rd_impl_conn, rd_name_conn, rd_disconn
);
 

endmodule

*/