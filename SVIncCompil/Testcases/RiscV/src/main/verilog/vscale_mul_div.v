`include "vscale_md_constants.vh"
`include "vscale_ctrl_constants.vh"
`include "rv32_opcodes.vh"

module vscale_mul_div(
                      input                         clk,
                      input                         reset,
                      input                         req_valid,
                      output                        req_ready,
                      input                         req_in_1_signed,
                      input                         req_in_2_signed,
                      input [`MD_OP_WIDTH-1:0]      req_op,
                      input [`MD_OUT_SEL_WIDTH-1:0] req_out_sel,
                      input [`XPR_LEN-1:0]          req_in_1,
                      input [`XPR_LEN-1:0]          req_in_2,
                      output                        resp_valid,
                      output [`XPR_LEN-1:0]         resp_result
                      );

   localparam md_state_width = 2;
   localparam s_idle = 0;
   localparam s_compute = 1;
   localparam s_setup_output = 2;
   localparam s_done = 3;

   reg [md_state_width-1:0]                         state;
   reg [md_state_width-1:0]                         next_state;
   reg [`MD_OP_WIDTH-1:0]                           op;
   reg [`MD_OUT_SEL_WIDTH-1:0]                      out_sel;
   reg                                              negate_output;
   reg [`DOUBLE_XPR_LEN-1:0]                        a;
   reg [`DOUBLE_XPR_LEN-1:0]                        b;
   reg [`LOG2_XPR_LEN-1:0]                          counter;
   reg [`DOUBLE_XPR_LEN-1:0]                        result;

   wire [`XPR_LEN-1:0]                              abs_in_1;
   wire                                             sign_in_1;
   wire [`XPR_LEN-1:0]                              abs_in_2;
   wire                                             sign_in_2;

   wire                                             a_geq;
   wire [`DOUBLE_XPR_LEN-1:0]                       result_muxed;
   wire [`DOUBLE_XPR_LEN-1:0]                       result_muxed_negated;
   wire [`XPR_LEN-1:0]                              final_result;

   function [`XPR_LEN-1:0] abs_input;
      input [`XPR_LEN-1:0]                          data;
      input                                         is_signed;
      begin
         abs_input = (data[`XPR_LEN-1] == 1'b1 && is_signed) ? -data : data;
      end
   endfunction // if

   assign req_ready = (state == s_idle);
   assign resp_valid = (state == s_done);
   assign resp_result = result[`XPR_LEN-1:0];

   assign abs_in_1 = abs_input(req_in_1,req_in_1_signed);
   assign sign_in_1 = req_in_1_signed && req_in_1[`XPR_LEN-1];
   assign abs_in_2 = abs_input(req_in_2,req_in_2_signed);
   assign sign_in_2 = req_in_2_signed && req_in_2[`XPR_LEN-1];

   assign a_geq = a >= b;
   assign result_muxed = (out_sel == `MD_OUT_REM) ? a : result;
   assign result_muxed_negated = (negate_output) ? -result_muxed : result_muxed;
   assign final_result = (out_sel == `MD_OUT_HI) ? result_muxed_negated[`XPR_LEN+:`XPR_LEN] : result_muxed_negated[0+:`XPR_LEN];

   always @(posedge clk) begin
      if (reset) begin
         state <= s_idle;
      end else begin
         state <= next_state;
      end
   end

   always @(*) begin
      case (state)
        s_idle : next_state = (req_valid) ? s_compute : s_idle;
        s_compute : next_state = (counter == 0) ? s_setup_output : s_compute;
        s_setup_output : next_state = s_done;
        s_done : next_state = s_idle;
        default : next_state = s_idle;
      endcase // case (state)
   end

   always @(posedge clk) begin
      case (state)
        s_idle : begin
           if (req_valid) begin
              result <= 0;
              a <= {`XPR_LEN'b0,abs_in_1};
              b <= {abs_in_2,`XPR_LEN'b0} >> 1;
              negate_output <= (op == `MD_OP_REM) ? sign_in_1 : sign_in_1 ^ sign_in_2;
              out_sel <= req_out_sel;
              op <= req_op;
              counter <= `XPR_LEN - 1;
           end
        end
        s_compute : begin
           counter <= counter - 1;
           b <= b >> 1;
           if (op == `MD_OP_MUL) begin
              if (a[counter]) begin
                 result <= result + b;
              end
           end else begin
              b <= b >> 1;
              if (a_geq) begin
                 a <= a - b;
                 result <= (`DOUBLE_XPR_LEN'b1 << counter) | result;
              end
           end
        end // case: s_compute
        s_setup_output : begin
           result <= {`XPR_LEN'b0,final_result};
        end
      endcase // case (state)
   end // always @ (posedge clk)

endmodule // vscale_mul_div

