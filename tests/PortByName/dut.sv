module top();
  logic [33:0] top_second[2];
  logic [33:0] top_third[2];
  logic [1:0]  top_first;
  ibex_id_stage id_stage_i (
      .third              ( top_third            ),
      .first              ( top_first            ),
      .second             ( top_second           )
  );

endmodule
module ibex_id_stage (
    input  logic [1:0]                first,
    input  logic [33:0]               second[2],
    output logic [33:0]               third[2]
);
  logic [33:0] fourth[2];
  assign third = fourth;

endmodule

