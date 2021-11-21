module tbcm_mux #(
  parameter   int   WIDTH         = 2,
  parameter   type  DATA_TYPE     = logic [WIDTH-1:0],
  parameter   int   ENTRIES       = 2,
  parameter   bit   ONE_HOT       = 1,
  localparam  int   INDEX_WIDTH   = (ENTRIES >= 2) ? $clog2(ENTRIES) : 1,
  localparam  int   SELECT_WIDTH  = (ONE_HOT) ? ENTRIES : INDEX_WIDTH
)(
  input   logic [SELECT_WIDTH-1:0]  i_select,
  input   DATA_TYPE                 i_data[ENTRIES],
  output  DATA_TYPE                 o_data
);
  logic [INDEX_WIDTH-1:0] index;

  assign  o_data  = i_data[index];
  if (ENTRIES == 1) begin
    assign  index = 0;
  end
  else if (ONE_HOT) begin
    assign  index = get_index(i_select);
  end
  else begin
    assign  index = i_select;
  end

  function automatic logic [INDEX_WIDTH-1:0] get_index(
    logic [SELECT_WIDTH-1:0]  select
  );
    logic [INDEX_WIDTH-1:0] index;

    for (int i = 0;i < INDEX_WIDTH;++i) begin
      logic [ENTRIES-1:0] temp;
      for (int j = 0;j < ENTRIES;++j) begin
        temp[j] = select[j] & j[i];
      end
      index[i]  = |temp;
    end

    return index;
  endfunction
endmodule
