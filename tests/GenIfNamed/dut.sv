
module top();

  for (i = 0; i < 3 ; i = i + 1) begin: tag1
     if (1) begin: tag2
        assign tmp[i] = 1'b1;
     end else begin: tag3
        assign tmp[i] = 1'b0;
     end
  end

endmodule