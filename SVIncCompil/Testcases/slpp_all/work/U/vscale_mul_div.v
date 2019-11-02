// Width-related constants


// Opcodes



// 7'b1101011 is reserved



// 7'b1010111 is reserved
// 7'b1110111 is reserved

// 7'b0011011 is RV64-specific
// 7'b0111011 is RV64-specific

// Arithmetic FUNCT3 encodings


// Branch FUNCT3 encodings


// MISC-MEM FUNCT3 encodings

// SYSTEM FUNCT3 encodings


// PRIV FUNCT12 encodings


// RV32M encodings


module vscale_mul_div(
                      input                         clk,
                      input                         reset,
                      input                         req_valid,
                      output                        req_ready,
                      input                         req_in_1_signed,
                      input                         req_in_2_signed,
                      input [2-1:0]      req_op,
                      input [2-1:0] req_out_sel,
                      input [32-1:0]          req_in_1,
                      input [32-1:0]          req_in_2,
                      output                        resp_valid,
                      output [32-1:0]         resp_result
                      );

   localparam md_state_width = 2;
   localparam s_idle = 0;
   localparam s_compute = 1;
   localparam s_setup_output = 2;
   localparam s_done = 3;

   reg [md_state_width-1:0]                         state;
   reg [md_state_width-1:0]                         next_state;
   reg [2-1:0]                           op;
   reg [2-1:0]                      out_sel;
   reg                                              negate_output;
   reg [64-1:0]                        a;
   reg [64-1:0]                        b;
   reg [5-1:0]                          counter;
   reg [64-1:0]                        result;

   wire [32-1:0]                              abs_in_1;
   wire                                             sign_in_1;
   wire [32-1:0]                              abs_in_2;
   wire                                             sign_in_2;

   wire                                             a_geq;
   wire [64-1:0]                       result_muxed;
   wire [64-1:0]                       result_muxed_negated;
   wire [32-1:0]                              final_result;

   function [32-1:0] abs_input;
      input [32-1:0]                          data;
      input                                         is_signed;
      begin
         abs_input = (data[32-1] ==  1'b1&& is_signed) ? -data : data;
      end
   endfunction // if

   assign req_ready = (state == s_idle);
   assign resp_valid = (state == s_done);
   assign resp_result = result[32-1:0];

   assign abs_in_1 = abs_input(req_in_1,req_in_1_signed);
   assign sign_in_1 = req_in_1_signed && req_in_1[32-1];
   assign abs_in_2 = abs_input(req_in_2,req_in_2_signed);
   assign sign_in_2 = req_in_2_signed && req_in_2[32-1];

   assign a_geq = a >= b;
   assign result_muxed = (out_sel == 2'd2) ? a : result;
   assign result_muxed_negated = (negate_output) ? -result_muxed : result_muxed;
   assign final_result = (out_sel == 2'd1) ? result_muxed_negated[32+:32] : result_muxed_negated[0+:32];

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
              a <= {32'b0,abs_in_1};
              b <= {abs_in_2,32'b0} >> 1;
              negate_output <= (op == 2'd2) ? sign_in_1 : sign_in_1 ^ sign_in_2;
              out_sel <= req_out_sel;
              op <= req_op;
              counter <=  32- 1;
           end
        end
        s_compute : begin
           counter <= counter - 1;
           b <= b >> 1;
           if (op == 2'd0) begin
              if (a[counter]) begin
                 result <= result + b;
              end
           end else begin
              b <= b >> 1;
              if (a_geq) begin
                 a <= a - b;
                 result <= ( 64'b1<< counter) | result;
              end
           end
        end // case: s_compute
        s_setup_output : begin
           result <= {32'b0,final_result};
        end
      endcase // case (state)
   end // always @ (posedge clk)

endmodule // vscale_mul_div

