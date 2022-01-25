module aes_sbox
(
  input  logic [3:0][3:0][7:0] data_i
);

endmodule

module aes_sub_bytes #(
) (
  input  logic [3:0][3:0][7:0] data_i
);

  // Individually substitute bytes
  for (genvar j = 0; j < 2; j++) begin : gen_sbox_j
    for (genvar i = 0; i < 2; i++) begin : gen_sbox_i
      aes_sbox #(
      ) aes_sbox_ij (
        .data_i ( data_i[i][j] )
      );
    end
  end

endmodule

