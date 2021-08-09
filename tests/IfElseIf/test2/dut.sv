module GOOD();
endmodule

module axi();

    parameter j = 3;  
    parameter LOG_MASTER      = 5;

    generate

      if (j == 0 )  begin : LAST_NODE
                         
      end else if ( j < LOG_MASTER - 1)  begin : MIDDLE_NODES // START of MIDDLE LEVELS Nodes
            GOOD good();                          
          end 
          else begin : LEAF_NODES  // START of FIRST LEVEL Nodes (LEAF)
          end 
    endgenerate

endmodule

