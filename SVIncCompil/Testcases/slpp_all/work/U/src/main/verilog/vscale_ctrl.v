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


module vscale_ctrl(
                   input                              clk,
                   input                              reset,
                   input [32-1:0]            inst_DX,
                   input                              imem_wait,
                   input                              imem_badmem_e,
                   input                              dmem_wait,
                   input                              dmem_badmem_e,
                   input                              cmp_true,
                   input [2-1:0]             prv,
                   output reg [3-1:0] PC_src_sel,
                   output reg [2-1:0]   imm_type,
                   output                             bypass_rs1,
                   output                             bypass_rs2,
                   output reg [2-1:0]  src_a_sel,
                   output reg [2-1:0]  src_b_sel,
                   output reg [4-1:0]     alu_op,
                   output wire                        dmem_en,
                   output wire                        dmem_wen,
                   output wire [2:0]                  dmem_size,
                   output wire [3-1:0]  dmem_type,
                   output                             md_req_valid,
                   input                              md_req_ready,
                   output reg                         md_req_in_1_signed,
                   output reg                         md_req_in_2_signed,
                   output reg [2-1:0]      md_req_op,
                   output reg [2-1:0] md_req_out_sel,
                   input                              md_resp_valid,
                   output wire                        eret,
                   output [3-1:0]        csr_cmd,
                   output reg                         csr_imm_sel,
                   input                              illegal_csr_access,
		   input                              interrupt_pending,
		   input                              interrupt_taken,
                   output wire                        wr_reg_WB,
                   output reg [5-1:0]   reg_to_wr_WB,
                   output reg [2-1:0] wb_src_sel_WB,
                   output wire                        stall_IF,
                   output wire                        kill_IF,
                   output wire                        stall_DX,
                   output wire                        kill_DX,
                   output wire                        stall_WB,
                   output wire                        kill_WB,
                   output wire                        exception_WB,
                   output wire [4-1:0]     exception_code_WB,
                   output wire                        retire_WB
                   );

   // IF stage ctrl pipeline registers
   reg                                                replay_IF;

   // IF stage ctrl signals
   wire                                               ex_IF;

   // DX stage ctrl pipeline registers
   reg                                                had_ex_DX;
   reg                                                prev_killed_DX;

   // DX stage ctrl signals
   wire [6:0]                                         opcode = inst_DX[6:0];
   wire [6:0]                                         funct7 = inst_DX[31:25];
   wire [11:0]                                        funct12 = inst_DX[31:20];
   wire [2:0]                                         funct3 = inst_DX[14:12];
   wire [5-1:0]                         rs1_addr = inst_DX[19:15];
   wire [5-1:0]                         rs2_addr = inst_DX[24:20];
   wire [5-1:0]                         reg_to_wr_DX = inst_DX[11:7];
   reg                                                illegal_instruction;
   reg                                                ebreak;
   reg                                                ecall;
   reg                                                eret_unkilled;
   reg                                                fence_i;
   wire [4-1:0]                           add_or_sub;
   wire [4-1:0]                           srl_or_sra;
   reg [4-1:0]                            alu_op_arith;
   reg                                                branch_taken_unkilled;
   wire                                               branch_taken;
   reg                                                dmem_en_unkilled;
   reg                                                dmem_wen_unkilled;
   reg                                                jal_unkilled;
   wire                                               jal;
   reg                                                jalr_unkilled;
   wire                                               jalr;
   wire                                               redirect;
   reg                                                wr_reg_unkilled_DX;
   wire                                               wr_reg_DX;
   reg [2-1:0]                        wb_src_sel_DX;
   wire                                               new_ex_DX;
   wire                                               ex_DX;
   reg [4-1:0]                             ex_code_DX;
   wire                                               killed_DX;
   reg                                                uses_md_unkilled;
   wire                                               uses_md;
   reg 						      wfi_unkilled_DX;
   wire 					      wfi_DX;
   reg [3-1:0]                           csr_cmd_unkilled;
   
   // WB stage ctrl pipeline registers
   reg                                                wr_reg_unkilled_WB;
   reg                                                had_ex_WB;
   reg [4-1:0]                             prev_ex_code_WB;
   reg                                                store_in_WB;
   reg                                                dmem_en_WB;
   reg                                                prev_killed_WB;
   reg                                                uses_md_WB;
   reg 						      wfi_unkilled_WB;
   
   // WB stage ctrl signals
   wire                                               ex_WB;
   reg [4-1:0]                             ex_code_WB;
   wire                                               dmem_access_exception;
   wire                                               exception = ex_WB;
   wire                                               killed_WB;
   wire                                               load_in_WB;
   wire 					      active_wfi_WB;
   
   // Hazard signals
   wire                                               load_use;
   reg                                                uses_rs1;
   reg                                                uses_rs2;
   wire                                               raw_rs1;
   wire                                               raw_rs2;
   wire                                               raw_on_busy_md;

   // IF stage ctrl

   always @(posedge clk) begin
      if (reset) begin
         replay_IF <= 1'b1;
      end else begin
         replay_IF <= (redirect && imem_wait) || (fence_i && store_in_WB);
      end
   end

   // interrupts kill IF, DX instructions -- WB may commit
   assign kill_IF = stall_IF || ex_IF || ex_DX || ex_WB || redirect || replay_IF || interrupt_taken;
   assign stall_IF = stall_DX ||
                     ((imem_wait && !redirect) && !(ex_WB || interrupt_taken));
   assign ex_IF = imem_badmem_e && !imem_wait && !redirect && !replay_IF;

   // DX stage ctrl

   always @(posedge clk) begin
      if (reset) begin
         had_ex_DX <= 0;
         prev_killed_DX <= 0;
      end else if (!stall_DX) begin
         had_ex_DX <= ex_IF;
         prev_killed_DX <= kill_IF;
      end
   end

   // interrupts kill IF, DX instructions -- WB may commit
   // Exceptions never show up falsely due to hazards -- don't get exceptions on stall
   assign kill_DX = stall_DX || ex_DX || ex_WB || interrupt_taken;
   assign stall_DX = stall_WB ||
                     (( // internal hazards
                        load_use ||
                        raw_on_busy_md ||
                        (fence_i && store_in_WB) ||
                        (uses_md_unkilled && !md_req_ready)
                        ) && !(ex_DX || ex_WB || interrupt_taken));
   assign new_ex_DX = ebreak || ecall || illegal_instruction || illegal_csr_access;
   assign ex_DX = had_ex_DX || new_ex_DX; // TODO: add causes
   assign killed_DX = prev_killed_DX || kill_DX;

   always @(*) begin
      ex_code_DX = 0;
      if (had_ex_DX) begin
         ex_code_DX = 0;
      end else if (illegal_instruction) begin
         ex_code_DX = 2;
      end else if (illegal_csr_access) begin
         ex_code_DX = 2;
      end else if (ebreak) begin
         ex_code_DX = 3;
      end else if (ecall) begin
         ex_code_DX =  8+ prv;
      end
   end // always @ begin


   /*
    Note: the convention is to use an initial default
    assignment for all control signals (except for
    illegal instructions) and override the default
    values when appropriate, rather than using the
    default keyword. The exception is for illegal
    instructions; in the interest of brevity, this
    signal is set in the default case of any case
    statement after initially being zero.
    */

   assign dmem_size = {1'b0,funct3[1:0]};
   assign dmem_type = funct3;

   always @(*) begin
      illegal_instruction = 1'b0;
      csr_cmd_unkilled = 0;
      csr_imm_sel = funct3[2];
      ecall = 1'b0;
      ebreak = 1'b0;
      eret_unkilled = 1'b0;
      fence_i = 1'b0;
      branch_taken_unkilled = 1'b0;
      jal_unkilled = 1'b0;
      jalr_unkilled = 1'b0;
      uses_rs1 = 1'b1;
      uses_rs2 = 1'b0;
      imm_type = 2'd0;
      src_a_sel = 2'd0;
      src_b_sel = 2'd1;
      alu_op = 4'd0;
      dmem_en_unkilled = 1'b0;
      dmem_wen_unkilled = 1'b0;
      wr_reg_unkilled_DX = 1'b0;
      wb_src_sel_DX = 2'd0;
      uses_md_unkilled = 1'b0;
      wfi_unkilled_DX = 1'b0;
      case (opcode)
         7'b0000011: begin
           dmem_en_unkilled = 1'b1;
           wr_reg_unkilled_DX = 1'b1;
           wb_src_sel_DX = 2'd1;
        end
         7'b0100011: begin
           uses_rs2 = 1'b1;
           imm_type = 2'd1;
           dmem_en_unkilled = 1'b1;
           dmem_wen_unkilled = 1'b1;
        end
         7'b1100011: begin
           uses_rs2 = 1'b1;
           branch_taken_unkilled = cmp_true;
           src_b_sel = 2'd0;
           case (funct3)
              0: alu_op = 4'd8;
              1: alu_op = 4'd9;
              4: alu_op = 4'd12;
              6: alu_op = 4'd14;
              5: alu_op = 4'd13;
              7: alu_op = 4'd15;
             default : illegal_instruction = 1'b1;
           endcase // case (funct3)
        end
         7'b1101111: begin
           jal_unkilled = 1'b1;
           uses_rs1 = 1'b0;
           src_a_sel = 2'd1;
           src_b_sel = 2'd2;
           wr_reg_unkilled_DX = 1'b1;
        end
         7'b1100111: begin
           illegal_instruction = (funct3 != 0);
           jalr_unkilled = 1'b1;
           src_a_sel = 2'd1;
           src_b_sel = 2'd2;
           wr_reg_unkilled_DX = 1'b1;
        end
         7'b0001111: begin
           case (funct3)
              0: begin
                if ((inst_DX[31:28] == 0) && (rs1_addr == 0) && (reg_to_wr_DX == 0))
                  ; // most fences are no-ops
                else
                  illegal_instruction = 1'b1;
             end
              1: begin
                if ((inst_DX[31:20] == 0) && (rs1_addr == 0) && (reg_to_wr_DX == 0))
                  fence_i = 1'b1;
                else
                  illegal_instruction = 1'b1;
             end
             default : illegal_instruction = 1'b1;
           endcase // case (funct3)
        end
         7'b0010011: begin
           alu_op = alu_op_arith;
           wr_reg_unkilled_DX = 1'b1;
        end
         7'b0110011: begin
           uses_rs2 = 1'b1;
           src_b_sel = 2'd0;
           alu_op = alu_op_arith;
           wr_reg_unkilled_DX = 1'b1;
           if (funct7 == 7'd1) begin
              uses_md_unkilled = 1'b1;
              wb_src_sel_DX = 2'd3;
           end
        end
         7'b1110011: begin
           wb_src_sel_DX = 2'd2;
           wr_reg_unkilled_DX = (funct3 != 0);
           case (funct3)
              0: begin
                if ((rs1_addr == 0) && (reg_to_wr_DX == 0)) begin
                   case (funct12)
                      12'b000000000000: ecall = 1'b1;
                      12'b000000000001: ebreak = 1'b1;
                      12'b000100000000: begin
                        if (prv == 0)
                          illegal_instruction = 1'b1;
                        else
                          eret_unkilled = 1'b1;
                     end
		      12'b000100000010: wfi_unkilled_DX = 1'b1;
                     default : illegal_instruction = 1'b1;
                   endcase // case (funct12)
                end // if ((rs1_addr == 0) && (reg_to_wr_DX == 0))
             end // case: `RV32_FUNCT3_PRIV
              1: csr_cmd_unkilled = (rs1_addr == 0) ?  4: 5;
              2: csr_cmd_unkilled = (rs1_addr == 0) ?  4: 6;
              3: csr_cmd_unkilled = (rs1_addr == 0) ?  4: 7;
              5: csr_cmd_unkilled = (rs1_addr == 0) ?  4: 5;
              6: csr_cmd_unkilled = (rs1_addr == 0) ?  4: 6;
              7: csr_cmd_unkilled = (rs1_addr == 0) ?  4: 7;
             default : illegal_instruction = 1'b1;
           endcase // case (funct3)
        end
         7'b0010111: begin
           uses_rs1 = 1'b0;
           src_a_sel = 2'd1;
           imm_type = 2'd2;
           wr_reg_unkilled_DX = 1'b1;
        end
         7'b0110111: begin
           uses_rs1 = 1'b0;
           src_a_sel = 2'd2;
           imm_type = 2'd2;
           wr_reg_unkilled_DX = 1'b1;
        end
        default : begin
           illegal_instruction = 1'b1;
        end
      endcase // case (opcode)
   end // always @ (*)

   assign add_or_sub = ((opcode == 7'b0110011) && (funct7[5])) ?  4'd10: 4'd0;
   assign srl_or_sra = (funct7[5]) ?  4'd11: 4'd5;

   assign md_req_valid = uses_md;

   always @(*) begin
      md_req_op = 2'd0;
      md_req_in_1_signed = 0;
      md_req_in_2_signed = 0;
      md_req_out_sel = 2'd0;
      case (funct3)
         3'd0: begin
        end
         3'd1: begin
           md_req_in_1_signed = 1;
           md_req_in_2_signed = 1;
           md_req_out_sel = 2'd1;
        end
         3'd2: begin
           md_req_in_1_signed = 1;
           md_req_out_sel = 2'd1;
        end
         3'd3: begin
           md_req_out_sel = 2'd1;
        end
         3'd4: begin
           md_req_op = 2'd1;
           md_req_in_1_signed = 1;
           md_req_in_2_signed = 1;
        end
         3'd5: begin
           md_req_op = 2'd1;
        end
         3'd6: begin
           md_req_op = 2'd2;
           md_req_in_1_signed = 1;
           md_req_in_2_signed = 1;
           md_req_out_sel = 2'd2;
        end
         3'd7: begin
           md_req_op = 2'd2;
           md_req_out_sel = 2'd2;
        end
      endcase
   end

   always @(*) begin
      case (funct3)
         0: alu_op_arith = add_or_sub;
         1: alu_op_arith = 4'd1;
         2: alu_op_arith = 4'd12;
         3: alu_op_arith = 4'd14;
         4: alu_op_arith = 4'd4;
         5: alu_op_arith = srl_or_sra;
         6: alu_op_arith = 4'd6;
         7: alu_op_arith = 4'd7;
        default : alu_op_arith = 4'd0;
      endcase // case (funct3)
   end // always @ begin

   assign branch_taken = branch_taken_unkilled && !kill_DX;
   assign jal = jal_unkilled && !kill_DX;
   assign jalr = jalr_unkilled && !kill_DX;
   assign eret = eret_unkilled && !kill_DX;
   assign dmem_en = dmem_en_unkilled && !kill_DX;
   assign dmem_wen = dmem_wen_unkilled && !kill_DX;
   assign wr_reg_DX = wr_reg_unkilled_DX && !kill_DX;
   assign uses_md = uses_md_unkilled && !kill_DX;
   assign wfi_DX = wfi_unkilled_DX && !kill_DX;
   assign csr_cmd = (kill_DX) ?  0: csr_cmd_unkilled;
   assign redirect = branch_taken || jal || jalr || eret;

   always @(*) begin
      if (exception || interrupt_taken) begin
         PC_src_sel = 3'd5;
      end else if (replay_IF || (stall_IF && !imem_wait)) begin
         PC_src_sel = 3'd4;
      end else if (eret) begin
         PC_src_sel = 3'd6;
      end else if (branch_taken) begin
         PC_src_sel = 3'd1;
      end else if (jal) begin
         PC_src_sel = 3'd2;
      end else if (jalr) begin
         PC_src_sel = 3'd3;
      end else begin
         PC_src_sel = 3'd0;
      end
   end // always @ begin

   // WB stage ctrl

   always @(posedge clk) begin
      if (reset) begin
         prev_killed_WB <= 0;
         had_ex_WB <= 0;
         wr_reg_unkilled_WB <= 0;
         store_in_WB <= 0;
         dmem_en_WB <= 0;
         uses_md_WB <= 0;
	 wfi_unkilled_WB <= 0;
      end else if (!stall_WB) begin
         prev_killed_WB <= killed_DX;
         had_ex_WB <= ex_DX;
         wr_reg_unkilled_WB <= wr_reg_DX;
         wb_src_sel_WB <= wb_src_sel_DX;
         prev_ex_code_WB <= ex_code_DX;
         reg_to_wr_WB <= reg_to_wr_DX;
         store_in_WB <= dmem_wen;
         dmem_en_WB <= dmem_en;
         uses_md_WB <= uses_md;
	 wfi_unkilled_WB <= wfi_DX;
      end
   end

   // WFI handling
   // can't be killed while in WB stage
   assign active_wfi_WB = !prev_killed_WB && wfi_unkilled_WB 
			  && !(interrupt_taken || interrupt_pending);

   assign kill_WB = stall_WB || ex_WB;
   assign stall_WB = ((dmem_wait && dmem_en_WB) || (uses_md_WB && !md_resp_valid) || active_wfi_WB) && !exception;
   assign dmem_access_exception = dmem_badmem_e;
   assign ex_WB = had_ex_WB || dmem_access_exception;
   assign killed_WB = prev_killed_WB || kill_WB;

   always @(*) begin
      ex_code_WB = prev_ex_code_WB;
      if (!had_ex_WB) begin
         if (dmem_access_exception) begin
            ex_code_WB = wr_reg_unkilled_WB ?
                          4:
                         6;
         end
      end
   end

   assign exception_WB = ex_WB;
   assign exception_code_WB = ex_code_WB;
   assign wr_reg_WB = wr_reg_unkilled_WB && !kill_WB;
   assign retire_WB = !(kill_WB || killed_WB);

   // Hazard logic

   assign load_in_WB = dmem_en_WB && !store_in_WB;

   assign raw_rs1 = wr_reg_WB && (rs1_addr == reg_to_wr_WB)
     && (rs1_addr != 0) && uses_rs1;
   assign bypass_rs1 = !load_in_WB && raw_rs1;

   assign raw_rs2 = wr_reg_WB && (rs2_addr == reg_to_wr_WB)
     && (rs2_addr != 0) && uses_rs2;
   assign bypass_rs2 = !load_in_WB && raw_rs2;

   assign raw_on_busy_md = uses_md_WB && (raw_rs1 || raw_rs2) && !md_resp_valid;
   assign load_use = load_in_WB && (raw_rs1 || raw_rs2);

endmodule // vscale_ctrl
