interface tbcm_selector #(
  parameter int       WIDTH     = 8,
  parameter type      DATA_TYPE = logic [WIDTH-1:0],
  parameter int       ENTRIES   = 2,
  parameter bit       ONE_HOT   = 1,
  parameter DATA_TYPE DEFAULT   = DATA_TYPE'(0)
);
  localparam  int INDEX_WIDTH   = (ENTRIES >= 2) ? $clog2(ENTRIES) : 1;
  localparam  int SELECT_WIDTH  = (ONE_HOT) ? ENTRIES : INDEX_WIDTH;

  function automatic logic [INDEX_WIDTH-1:0] get_index(
    logic [SELECT_WIDTH-1:0]  select
  );
    if (ENTRIES == 1) begin
      return 0;
    end
    else if (ONE_HOT) begin
      return one_hot_to_binary(select);
    end
    else begin
      return select;
    end
  endfunction

  function automatic logic [INDEX_WIDTH-1:0] one_hot_to_binary(
    logic [ENTRIES-1:0] select
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

  function automatic DATA_TYPE mux(
    logic [SELECT_WIDTH-1:0]  select,
    DATA_TYPE [ENTRIES-1:0]   data
  );
    logic [INDEX_WIDTH-1:0] index;
    index = get_index(select);
    return data[index];
  endfunction

  function automatic DATA_TYPE [ENTRIES-1:0] demux(
    logic [SELECT_WIDTH-1:0]  select,
    DATA_TYPE                 data
  );
    DATA_TYPE [ENTRIES-1:0] demuxed_data;

    for (int i = 0;i < ENTRIES;++i) begin
      if (ONE_HOT && select[i]) begin
        demuxed_data[i] = data;
      end
      else if ((!ONE_HOT) && (select == i)) begin
        demuxed_data[i] = data;
      end
      else begin
        demuxed_data[i] = DEFAULT;
      end
    end

    return demuxed_data;
  endfunction
endinterface

