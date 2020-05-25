module small_test();

  parameter signed [3:0] SIZE = 5;

  genvar i, m; 
  generate
    for (i=0; i<SIZE; i=i+1) begin :B1
  
        M1 N1();
      
        if (i>=1) begin :B4
            for (m=i; m<SIZE; m=m+1) begin :B5  
                M4 N4();
            end
        end
    end
  endgenerate

endmodule

