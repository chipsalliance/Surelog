module top(input rd_impl_conn, rd_name_conn);
   ibex_csr #(
   ) u_mie_csr (
     .rd_impl_conn,
     .rd_name_conn(rd_name_conn),
     .rd_disconn(),
     .rd_const_conn(1'b1)	 	
   );
 
endmodule

module ibex_csr #(
 ) (
       input logic rd_const_conn,
       output logic rd_impl_conn, rd_name_conn, rd_disconn
);
 

endmodule
