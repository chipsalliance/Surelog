module bsg_wormhole_router
   
  #(
   parameter cord_dims_p = dims_p
   ,parameter int cord_markers_pos_p[cord_dims_p:0] =   '{ 5, 4, 0 }  // '{5,0} //
   ,parameter bit [1:0][dirs_lp-1:0][dirs_lp-1:0] routing_matrix_p =  (dims_p == 2) ? StrictXY : StrictX
   )

  (input clk_i
  ,input reset_i
  );

endmodule

module
     divSqrtRecFNToRaw_small#(

           parameter expWidth = 3, parameter sigWidth = 3, parameter options = 0

       ) ();

parameter p = 3;
generate 
if (p == 3)

      begin : threeronew
        M m1();

      end 


      bsg_wormhole_router

        #(
    
            .cord_dims_p(cord_dims_p)
    
            ,.cord_markers_pos_p(cord_markers_pos_p)
    
         
            ,.routing_matrix_p(routing_matrix_p)
    
         
    
            )
    
          router
    
         (.clk_i(network_clk_i)
    
          ,.reset_i(network_reset_i)
    
    
            );

endgenerate

endmodule

module
       isSigNaNRecFN#(parameter expWidth = 3, parameter sigWidth = 3) (
           input [(expWidth + sigWidth):0] in, output isSigNaN
       );
   
       wire isNaN =
           (in[(expWidth + sigWidth - 1):(expWidth + sigWidth - 3)] == 'b111);
       assign isSigNaN = isNaN && !in[sigWidth - 2];
    endmodule


module a ();

genvar v;

U1 u1();

endmodule


module b
();
endmodule

module c (

);
endmodule

module 
  d 
(

);
endmodule

module MOD (input a);
endmodule

module 
  e ();

  assign lce_resp_link_cast_o = '{data          : resp_concentrated_link_lo.data
                                        ,v            : resp_concentrated_link_lo.v
                                    ,ready_and_rev: cce_lce_resp_link_lo.ready_and_rev
                                    };
       
   MOD #(.p(

   ))
    u1 (
     .a({1,2
    }));

  
endmodule

module
     divSqrtRecFN_small#(

         parameter expWidth = 3, parameter sigWidth = 3, parameter options = 0

     )  (
     );



            if ((i == 2'b10) || (i == 2'b11))
              begin : atomic
                assign slice_data = decode_tv_r.amo_op
                 ? atomic_result[0+:slice_width_lp]
                 : st_data_tv_r[0+:slice_width_lp];
              end
            else
              begin : non_atomic
                assign slice_data = st_data_tv_r[0+:slice_width_lp];
              end
      
              if (mc_y_dim_p > 0)
                    begin : node
                       bp_l2e_tile_node
                        #(.bp_params_p(bp_params_p))
                         l2e
                          (.core_clk_i(core_clk_i)
                          ,.core_reset_i(core_reset_i)
                          );
                  end
              else
                begin : stub
                  assign lce_req_link_lo[i]  = '0;
                   assign lce_cmd_link_lo[i]  = '0;
             
                end
                  

endmodule