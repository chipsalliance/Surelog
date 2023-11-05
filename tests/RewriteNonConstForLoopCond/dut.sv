module top();

logic                  found;

   always_comb
     begin
        
        found = 1'b0;

        for (int i=0; i<32 && found==0; i++) begin
           if (cond == 1'b0) begin
             
           end
           else
              found=1'b1;
        end
     end


endmodule