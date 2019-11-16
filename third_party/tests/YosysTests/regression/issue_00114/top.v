module top(
  input wire clock
);

localparam COUNT = 1600;

reg buffer[0:COUNT-1];

always @(posedge clock) begin : GENERATE
  integer ii;

  for(ii = 0; ii < COUNT; ii = ii + 1) begin
    buffer[ii] <= 1'b0;
  end
end

endmodule
