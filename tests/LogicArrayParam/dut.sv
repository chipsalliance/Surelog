package alert_handler_reg_pkg;

  // Param list
  parameter int NAlerts = 20;
  parameter logic [NAlerts-1:0] AsyncOn = 20'b01100001100000001111;
endpackage


package alert_pkg;

  
  localparam int unsigned      NAlerts   = alert_handler_reg_pkg::NAlerts;   // maximum 252
  localparam bit [NAlerts-1:0] AsyncOn   = alert_handler_reg_pkg::AsyncOn;

endpackage

module M();
endmodule

module alert_handler
  import alert_pkg::*;
#() ();

  // Target interrupt notification
  for (genvar k = 0 ; k < NAlerts ; k++) begin : gen_alerts
    localparam debug = AsyncOn[k];
    if (debug) begin
      M u();
    end
  end 

endmodule


/*


module rggen_or_reducer #(
  parameter int WIDTH = 2,
  parameter int N     = 4
)(
 // input   logic [N-1:0][WIDTH-1:0]  i_data,
//  output  logic [WIDTH-1:0]         o_result
);

  function automatic bit [N-1:0][15:0] get_sub_n_list(int n);
    bit [N-1:0][15:0] list;
    int               list_index;
    bit [15:0]        current_n;
    bit [15:0]        half_n;

    list        = '0;
    list_index  = 0;
    current_n   = 16'(n);
    while (current_n > 0) begin
      half_n  = current_n / 2;
      if ((current_n > 4) && (half_n <= 4)) begin
        list[list_index]  = half_n;
      end
      else if (current_n >= 4) begin
        list[list_index]  = 4;
      end
      else begin
        list[list_index]  = current_n;
      end

      current_n   -= list[list_index];
      list_index  += 1;
    end

    return list;
  endfunction


  function automatic bit [N-1:0][15:0] get_offset_list(bit [N-1:0][15:0] sub_n_list);
    bit [N-1:0][15:0] list;

    for (int i = 0;i < N;++i) begin
      if (i == 0) begin
        list[i] = 0;
      end
      else begin
        list[i] = sub_n_list[i-1] + list[i-1];
      end
    end

    return list;
  endfunction

  function automatic int get_next_n(bit [N-1:0][15:0] sub_n_list);
    int next_n;

    next_n  = 0;
    for (int i = 0;i < N;++i) begin
      next_n  += ((sub_n_list[i] != 0) ? 1 : 0);
    end

    return next_n;
  endfunction

  localparam  bit [N-1:0][15:0] SUB_N_LIST_P  = get_sub_n_list(N);
  localparam  bit [N-1:0][15:0] OFFSET_LIST = get_offset_list(SUB_N_LIST_P);
  localparam  int               NEXT_N      = get_next_n(OFFSET_LIST);

  logic [NEXT_N-1:0][WIDTH-1:0] next_data;

endmodule
*/