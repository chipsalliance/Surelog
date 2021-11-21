module tbcm_counter #(
  parameter   int MAX_COUNT     = 3,
  parameter   int MIN_COUNT     = 0,
  parameter   int INITIAL_COUNT = MIN_COUNT,
  parameter   bit WRAP_AROUND   = 1,
  localparam  int WIDTH         = $clog2(MAX_COUNT + 1)
)(
  input   logic             clk,
  input   logic             rst_n,
  input   logic             i_clear,
  input   logic             i_set,
  input   logic [WIDTH-1:0] i_set_value,
  input   logic             i_up,
  input   logic             i_down,
  output  logic [WIDTH-1:0] o_count,
  output  logic [WIDTH-1:0] o_count_next
);
  localparam  bit [WIDTH-1:0] INITIAL = INITIAL_COUNT;
  localparam  bit [WIDTH-1:0] MAX     = MAX_COUNT;
  localparam  bit [WIDTH-1:0] MIN     = MIN_COUNT;

  logic [WIDTH-1:0] count;
  logic [WIDTH-1:0] count_next;

  assign  o_count       = count;
  assign  o_count_next  = count_next;
  assign  count_next    = get_count_next(
    .clear          (i_clear      ),
    .set            (i_set        ),
    .set_value      (i_set_value  ),
    .up             (i_up         ),
    .down           (i_down       ),
    .current_count  (count        )
  );

  always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      count <= INITIAL;
    end
    else begin
      count <= count_next;
    end
  end

  function automatic logic [WIDTH-1:0] get_count_next(
    input logic             clear,
    input logic             set,
    input logic [WIDTH-1:0] set_value,
    input logic             up,
    input logic             down,
    input logic [WIDTH-1:0] current_count
  );
    if (clear) begin
      return INITIAL;
    end
    else if (set) begin
      return set_value;
    end
    else if ({up, down} == 2'b10) begin
      return count_up(current_count);
    end
    else if ({up, down} == 2'b01) begin
      return count_down(current_count);
    end
    else begin
      return current_count;
    end
  endfunction

  function automatic logic [WIDTH-1:0] count_up(input logic [WIDTH-1:0] current_count);
    if (current_count == MAX) begin
      return (WRAP_AROUND) ? MIN : MAX;
    end
    else begin
      return current_count + 1;
    end
  endfunction

  function automatic logic [WIDTH-1:0] count_down(input logic [WIDTH-1:0] current_count);
    if (current_count == MIN) begin
      return (WRAP_AROUND) ? MAX : MIN;
    end
    else begin
      return count - 1;
    end
  endfunction
endmodule
