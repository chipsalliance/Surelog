module rggen_mux #(
  parameter int WIDTH   = 2,
  parameter int ENTRIES = 2
)(
  input   logic [ENTRIES-1:0]             i_select,
  input   logic [ENTRIES-1:0][WIDTH-1:0]  i_data,
  output  logic [WIDTH-1:0]               o_data
);
  generate
    if (ENTRIES >= 2) begin : g
      logic [ENTRIES-1:0][WIDTH-1:0]  masked_data;

      always_comb begin
        for (int i = 0;i < ENTRIES;++i) begin
          masked_data[i]  = i_data[i] & {WIDTH{i_select[i]}};
        end
      end

      rggen_or_reducer #(
        .WIDTH  (WIDTH    ),
        .N      (ENTRIES  )
      ) u_reducer (
        .i_data   (masked_data  ),
        .o_result (o_data       )
      );
    end
    else begin : g
      always_comb begin
        o_data  = i_data[0];
      end
    end
  endgenerate
endmodule
