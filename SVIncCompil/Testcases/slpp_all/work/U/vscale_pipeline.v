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


module vscale_pipeline(
                       input 			    clk,
		       input [24<EOF>-1:0] 	    ext_interrupts, 
                       input 			    reset,
                       input 			    imem_wait,
                       output [32-1:0] 	    imem_addr,
                       input [32-1:0] 	    imem_rdata,
                       input 			    imem_badmem_e,
                       input 			    dmem_wait,
                       output 			    dmem_en,
                       output 			    dmem_wen,
                       output [3-1:0] dmem_size,
                       output [32-1:0] 	    dmem_addr,
                       output [32-1:0] 	    dmem_wdata_delayed,
                       input [32-1:0] 	    dmem_rdata,
                       input 			    dmem_badmem_e,
                       input 			    htif_reset,
                       input 			    htif_pcr_req_valid,
                       output 			    htif_pcr_req_ready,
                       input 			    htif_pcr_req_rw,
                       input [12-1:0]  htif_pcr_req_addr,
                       input [64-1:0]  htif_pcr_req_data,
                       output 			    htif_pcr_resp_valid,
                       input 			    htif_pcr_resp_ready,
                       output [64-1:0] htif_pcr_resp_data
                       );

   function [32-1:0] store_data;
      input [32-1:0]                          addr;
      input [32-1:0]                          data;
      input [3-1:0]                   mem_type;
      begin
         case (mem_type)
            3'd0: store_data = {4{data[7:0]}};
            3'd1: store_data = {2{data[15:0]}};
           default : store_data = data;
         endcase // case (mem_type)
      end
   endfunction // case

   function [32-1:0] load_data;
      input [32-1:0]                      addr;
      input [32-1:0]                      data;
      input [3-1:0]               mem_type;
      reg [32-1:0]                        shifted_data;
      reg [32-1:0]                        b_extend;
      reg [32-1:0]                        h_extend;
      begin
         shifted_data = data >> {addr[1:0],3'b0};
         b_extend = {{24{shifted_data[7]}},8'b0};
         h_extend = {{16{shifted_data[15]}},16'b0};
         case (mem_type)
            3'd0: load_data = (shifted_data & 32'hff) | b_extend;
            3'd1: load_data = (shifted_data & 32'hffff) | h_extend;
            3'd4: load_data = (shifted_data & 32'hff);
            3'd5: load_data = (shifted_data & 32'hffff);
           default : load_data = shifted_data;
         endcase // case (mem_type)
      end
   endfunction // case

   wire [3-1:0]                 PC_src_sel;
   wire [32-1:0]                          PC_PIF;


   reg [32-1:0]                           PC_IF;

   wire                                         kill_IF;
   wire                                         stall_IF;


   reg [32-1:0]                           PC_DX;
   reg [32-1:0]                        inst_DX;

   wire                                         kill_DX;
   wire                                         stall_DX;
   wire [2-1:0]                   imm_type;
   wire [32-1:0]                          imm;
   wire [2-1:0]                  src_a_sel;
   wire [2-1:0]                  src_b_sel;
   wire [5-1:0]                   rs1_addr;
   wire [32-1:0]                          rs1_data;
   wire [32-1:0]                          rs1_data_bypassed;
   wire [5-1:0]                   rs2_addr;
   wire [32-1:0]                          rs2_data;
   wire [32-1:0]                          rs2_data_bypassed;
   wire [4-1:0]                     alu_op;
   wire [32-1:0]                          alu_src_a;
   wire [32-1:0]                          alu_src_b;
   wire [32-1:0]                          alu_out;
   wire                                         cmp_true;
   wire                                         bypass_rs1;
   wire                                         bypass_rs2;
   wire [3-1:0]                   dmem_type;

   wire                                         md_req_valid;
   wire                                         md_req_ready;
   wire                                         md_req_in_1_signed;
   wire                                         md_req_in_2_signed;
   wire [2-1:0]                 md_req_out_sel;
   wire [2-1:0]                      md_req_op;
   wire                                         md_resp_valid;
   wire [32-1:0]                          md_resp_result;

   reg [32-1:0]                           PC_WB;
   reg [32-1:0]                           alu_out_WB;
   reg [32-1:0]                           csr_rdata_WB;
   reg [32-1:0]                           store_data_WB;

   wire                                         kill_WB;
   wire                                         stall_WB;
   reg [32-1:0]                           bypass_data_WB;
   wire [32-1:0]                          load_data_WB;
   reg [32-1:0]                           wb_data_WB;
   wire [5-1:0]                   reg_to_wr_WB;
   wire                                         wr_reg_WB;
   wire [2-1:0]                 wb_src_sel_WB;
   reg [3-1:0]                    dmem_type_WB;

   // CSR management
   wire [12-1:0]                   csr_addr;
   wire [3-1:0]                    csr_cmd;
   wire                                         csr_imm_sel;
   wire [2-1:0]                        prv;
   wire                                         illegal_csr_access;
   wire 					interrupt_pending;
   wire 					interrupt_taken;
   wire [32-1:0]                          csr_wdata;
   wire [32-1:0]                          csr_rdata;
   wire                                         retire_WB;
   wire                                         exception_WB;
   wire [4-1:0]                      exception_code_WB;
   wire [32-1:0]                          handler_PC;
   wire                                         eret;
   wire [32-1:0]                          epc;

   vscale_ctrl ctrl(
                    .clk(clk),
                    .reset(reset),
                    .inst_DX(inst_DX),
                    .imem_wait(imem_wait),
                    .imem_badmem_e(imem_badmem_e),
                    .dmem_wait(dmem_wait),
                    .dmem_badmem_e(dmem_badmem_e),
                    .cmp_true(cmp_true),
                    .PC_src_sel(PC_src_sel),
                    .imm_type(imm_type),
                    .src_a_sel(src_a_sel),
                    .src_b_sel(src_b_sel),
                    .bypass_rs1(bypass_rs1),
                    .bypass_rs2(bypass_rs2),
                    .alu_op(alu_op),
                    .dmem_en(dmem_en),
                    .dmem_wen(dmem_wen),
                    .dmem_size(dmem_size),
                    .dmem_type(dmem_type),
                    .md_req_valid(md_req_valid),
                    .md_req_ready(md_req_ready),
                    .md_req_op(md_req_op),
                    .md_req_in_1_signed(md_req_in_1_signed),
                    .md_req_in_2_signed(md_req_in_2_signed),
                    .md_req_out_sel(md_req_out_sel),
                    .md_resp_valid(md_resp_valid),
                    .wr_reg_WB(wr_reg_WB),
                    .reg_to_wr_WB(reg_to_wr_WB),
                    .wb_src_sel_WB(wb_src_sel_WB),
                    .stall_IF(stall_IF),
                    .kill_IF(kill_IF),
                    .stall_DX(stall_DX),
                    .kill_DX(kill_DX),
                    .stall_WB(stall_WB),
                    .kill_WB(kill_WB),
                    .exception_WB(exception_WB),
                    .exception_code_WB(exception_code_WB),
                    .retire_WB(retire_WB),
                    .csr_cmd(csr_cmd),
                    .csr_imm_sel(csr_imm_sel),
                    .illegal_csr_access(illegal_csr_access),
		    .interrupt_pending(interrupt_pending),
		    .interrupt_taken(interrupt_taken),
                    .prv(prv),
                    .eret(eret)
                    );


   vscale_PC_mux PCmux(
                       .PC_src_sel(PC_src_sel),
                       .inst_DX(inst_DX),
                       .rs1_data(rs1_data_bypassed),
                       .PC_IF(PC_IF),
                       .PC_DX(PC_DX),
                       .handler_PC(handler_PC),
                       .epc(epc),
                       .PC_PIF(PC_PIF)
                       );

   assign imem_addr = PC_PIF;

   always @(posedge clk) begin
      if (reset) begin
         PC_IF <= 32'h200;
      end else if (~stall_IF) begin
         PC_IF <= PC_PIF;
      end
   end

   always @(posedge clk) begin
      if (reset) begin
         PC_DX <= 0;
         inst_DX <= 32'b0010011;
      end else if (~stall_DX) begin
         if (kill_IF) begin
            inst_DX <= 32'b0010011;
         end else begin
            PC_DX <= PC_IF;
            inst_DX <= imem_rdata;
         end
      end
   end // always @ (posedge hclk)

   assign rs1_addr = inst_DX[19:15];
   assign rs2_addr = inst_DX[24:20];

   vscale_regfile regfile(
                          .clk(clk),
                          .ra1(rs1_addr),
                          .rd1(rs1_data),
                          .ra2(rs2_addr),
                          .rd2(rs2_data),
                          .wen(wr_reg_WB),
                          .wa(reg_to_wr_WB),
                          .wd(wb_data_WB)
                          );

   vscale_imm_gen imm_gen(
                          .inst(inst_DX),
                          .imm_type(imm_type),
                          .imm(imm)
                          );

   vscale_src_a_mux src_a_mux(
                              .src_a_sel(src_a_sel),
                              .PC_DX(PC_DX),
                              .rs1_data(rs1_data_bypassed),
                              .alu_src_a(alu_src_a)
                              );

   vscale_src_b_mux src_b_mux(
                              .src_b_sel(src_b_sel),
                              .imm(imm),
                              .rs2_data(rs2_data_bypassed),
                              .alu_src_b(alu_src_b)
                              );

   assign rs1_data_bypassed = bypass_rs1 ? bypass_data_WB : rs1_data;
   assign rs2_data_bypassed = bypass_rs2 ? bypass_data_WB : rs2_data;

   vscale_alu alu(
                  .op(alu_op),
                  .in1(alu_src_a),
                  .in2(alu_src_b),
                  .out(alu_out)
                  );

   vscale_mul_div md(
                     .clk(clk),
                     .reset(reset),
                     .req_valid(md_req_valid),
                     .req_ready(md_req_ready),
                     .req_in_1_signed(md_req_in_1_signed),
                     .req_in_2_signed(md_req_in_2_signed),
                     .req_out_sel(md_req_out_sel),
                     .req_op(md_req_op),
                     .req_in_1(rs1_data_bypassed),
                     .req_in_2(rs2_data_bypassed),
                     .resp_valid(md_resp_valid),
                     .resp_result(md_resp_result)
                     );


   assign cmp_true = alu_out[0];


   assign dmem_addr = alu_out;

   always @(posedge clk) begin
      if (reset) begin
         PC_WB <= $random;
         store_data_WB <= $random;
         alu_out_WB <= $random;
      end else if (~stall_WB) begin
         PC_WB <= PC_DX;
         store_data_WB <= rs2_data_bypassed;
         alu_out_WB <= alu_out;
         csr_rdata_WB <= csr_rdata;
         dmem_type_WB <= dmem_type;
      end
   end


   always @(*) begin
      case (wb_src_sel_WB)
         2'd2: bypass_data_WB = csr_rdata_WB;
         2'd3: bypass_data_WB = md_resp_result;
        default : bypass_data_WB = alu_out_WB;
      endcase // case (wb_src_sel_WB)
   end

   assign load_data_WB = load_data(alu_out_WB,dmem_rdata,dmem_type_WB);

   always @(*) begin
      case (wb_src_sel_WB)
         2'd0: wb_data_WB = bypass_data_WB;
         2'd1: wb_data_WB = load_data_WB;
         2'd2: wb_data_WB = bypass_data_WB;
         2'd3: wb_data_WB = bypass_data_WB;
        default : wb_data_WB = bypass_data_WB;
      endcase
   end


   assign dmem_wdata_delayed = store_data(alu_out_WB,store_data_WB,dmem_type_WB);


   // CSR

   assign csr_addr = inst_DX[31:20];
   assign csr_wdata = (csr_imm_sel) ? inst_DX[19:15] : rs1_data_bypassed;

   vscale_csr_file csr(
                       .clk(clk),
		       .ext_interrupts(ext_interrupts),
                       .reset(reset),
                       .addr(csr_addr),
                       .cmd(csr_cmd),
                       .wdata(csr_wdata),
                       .prv(prv),
                       .illegal_access(illegal_csr_access),
                       .rdata(csr_rdata),
                       .retire(retire_WB),
                       .exception(exception_WB),
                       .exception_code(exception_code_WB),
                       .exception_load_addr(alu_out_WB),
                       .exception_PC(PC_WB),
                       .epc(epc),
                       .eret(eret),
                       .handler_PC(handler_PC),
		       .interrupt_pending(interrupt_pending),
		       .interrupt_taken(interrupt_taken),
                       .htif_reset(htif_reset),
                       .htif_pcr_req_valid(htif_pcr_req_valid),
                       .htif_pcr_req_ready(htif_pcr_req_ready),
                       .htif_pcr_req_rw(htif_pcr_req_rw),
                       .htif_pcr_req_addr(htif_pcr_req_addr),
                       .htif_pcr_req_data(htif_pcr_req_data),
                       .htif_pcr_resp_valid(htif_pcr_resp_valid),
                       .htif_pcr_resp_ready(htif_pcr_resp_ready),
                       .htif_pcr_resp_data(htif_pcr_resp_data)
                       );

endmodule // vscale_pipeline
