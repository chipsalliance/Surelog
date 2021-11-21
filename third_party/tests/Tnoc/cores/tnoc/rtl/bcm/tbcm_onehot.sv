interface tbcm_onehot #(
  parameter int WIDTH = 2
);
  if ((WIDTH > 2) && ((WIDTH % 2) == 1)) begin : g
    localparam  int HALF_WIDTH  = WIDTH / 2;
    tbcm_onehot #(HALF_WIDTH + 0) u_onehot_0();
    tbcm_onehot #(HALF_WIDTH + 1) u_onehot_1();

    function automatic logic [WIDTH-1:0] __onehot(logic [WIDTH-1:0] bits);
      logic [HALF_WIDTH-1:0]  result_0;
      logic [HALF_WIDTH-0:0]  result_1;
      logic [1:0]             ored;

      result_0  = u_onehot_0.to_onehot(bits[HALF_WIDTH-1:0]);
      ored[0]   = |{1'b0, result_0};
      result_1  = u_onehot_1.to_onehot(bits[WIDTH-1:HALF_WIDTH]);
      ored[1]   = |result_1;

      if (ored == 2'b10) begin
        return {result_1, {HALF_WIDTH{1'b0}}};
      end
      else begin
        return {{(HALF_WIDTH+1){1'b0}}, result_0};
      end
    endfunction
  end
  else if (WIDTH > 2) begin : g
    localparam  int HALF_WIDTH  = WIDTH / 2;
    tbcm_onehot #(HALF_WIDTH) u_onehot();

    function automatic logic [WIDTH-1:0] __onehot(logic [WIDTH-1:0] bits);
      logic [HALF_WIDTH-1:0]  result[2];
      logic [1:0]             ored;

      for (int i = 0;i < 2;++i) begin
        result[i] = u_onehot.to_onehot(bits[HALF_WIDTH*i+:HALF_WIDTH]);
        ored[i]   = |result[i];
      end

      if (ored == 2'b10) begin
        return {result[1], {HALF_WIDTH{1'b0}}};
      end
      else begin
        return {{HALF_WIDTH{1'b0}}, result[0]};
      end
    endfunction
  end
  else if (WIDTH == 2) begin : g
    function automatic logic [WIDTH-1:0] __onehot(logic [WIDTH-1:0] bits);
      if (bits == 2'b10) begin
        return bits;
      end
      else begin
        return {1'b0, bits[0]};
      end
    endfunction
  end
  else begin : g
    function automatic logic [WIDTH-1:0] __onehot(logic [WIDTH-1:0] bits);
      return bits;
    endfunction
  end

  function automatic logic [WIDTH-1:0] to_onehot(logic [WIDTH-1:0] bits);
    return g.__onehot(bits);
  endfunction
endinterface
