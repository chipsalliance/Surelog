module top (output logic [15:0] s0,s1,s2, o0,o1,o2, output logic [31:0] nn);
  localparam int N = 5;
  function automatic bit [N-1:0][15:0] gsl(int n);
    bit [N-1:0][15:0] list; int list_index; bit [15:0] current_n; bit [15:0] half_n;
    list = '0; list_index = 0; current_n = 16'(n);
    while (current_n > 0) begin
      half_n = current_n / 2;
      if ((current_n > 4) && (half_n <= 4)) list[list_index] = half_n;
      else if (current_n >= 4)             list[list_index] = 4;
      else                                 list[list_index] = current_n;
      current_n  -= list[list_index];
      list_index += 1;
    end
    return list;
  endfunction
  function automatic bit [N-1:0][15:0] gol(bit [N-1:0][15:0] sub);
    bit [N-1:0][15:0] list;
    for (int i = 0; i < N; ++i) begin
      if (i == 0) list[i] = 0; else list[i] = sub[i-1] + list[i-1];
    end
    return list;
  endfunction
  function automatic int gnn(bit [N-1:0][15:0] sub);
    int next_n = 0;
    for (int i = 0; i < N; ++i) next_n += ((sub[i] != 0) ? 1 : 0);
    return next_n;
  endfunction
  localparam bit [N-1:0][15:0] SUB = gsl(N);
  localparam bit [N-1:0][15:0] OFF = gol(SUB);
  localparam int NEXT = gnn(SUB);
  assign s0 = SUB[0]; assign s1 = SUB[1]; assign s2 = SUB[2];
  assign o0 = OFF[0]; assign o1 = OFF[1]; assign o2 = OFF[2];
  assign nn = NEXT;
  // Elaboration-visible consumers of the folded values: a generate-if arm
  // chosen by SUB[1] (3 at N = 5) and a net sized by OFF[2] (5).  With the
  // parameter mis-stored as UINT:1 the else arm is elaborated and the net is
  // [-1:0].
  if (SUB[1] == 3) begin : g_sub1_is_3
    logic [OFF[2]-1:0] w; assign w = '1;
  end else begin : g_sub1_not_3
    logic w; assign w = 1'b0;
  end
endmodule
