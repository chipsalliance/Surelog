module top#(
  // enables additional synchronization logic
  parameter bit AsyncOn = 1'b0
) ();

  if (AsyncOn) begin
  end else begin : gen_no_async
    logic diff_pq, diff_pd;

  end;

endmodule
