module socket_1n ();
  parameter bit [7:0] P1 = {1{4'h2, 4'h2}};
  parameter bit [7:0] P2 = {2{4'h2}};
  parameter bit [7:0] P3 = {1{4'b10, 4'h2}};
  parameter bit [7:0] P4 = {2{4'b10}};

  if (P1 == P2 && P2 == P3 && P3 == P4 && P4 == 34) begin
    GOOD good();
  end

endmodule
