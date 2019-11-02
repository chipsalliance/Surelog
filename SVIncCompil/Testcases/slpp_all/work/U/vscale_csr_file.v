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


module vscale_csr_file(
                       input 			    clk,
		       input [24<EOF>-1:0] 	    ext_interrupts, 
                       input 			    reset,
                       input [12-1:0]  addr,
                       input [3-1:0]   cmd,
                       input [32-1:0] 	    wdata,
                       output wire [2-1:0] prv,
                       output 			    illegal_access,
                       output reg [32-1:0]    rdata,
                       input 			    retire,
                       input 			    exception,
                       input [4-1:0]     exception_code,
                       input 			    eret,
                       input [32-1:0] 	    exception_load_addr,
                       input [32-1:0] 	    exception_PC,
                       output [32-1:0] 	    handler_PC,
                       output [32-1:0] 	    epc,
		       output 			    interrupt_pending,
		       output reg 		    interrupt_taken,
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

   localparam HTIF_STATE_IDLE = 0;
   localparam HTIF_STATE_WAIT = 1;

   reg [64-1:0]                        htif_rdata;
   reg [64-1:0]                        htif_resp_data;
   reg                                              htif_state;
   reg                                              htif_fire;
   reg                                              next_htif_state;

   reg [64-1:0]                     cycle_full;
   reg [64-1:0]                     time_full;
   reg [64-1:0]                     instret_full;
   reg [5:0]                                        priv_stack;
   reg [32-1:0]                               mtvec;
   reg [32-1:0] 				    mie;
   reg                                              mtip;
   reg                                              msip;
   reg [32-1:0]                               mtimecmp;
   reg [64-1:0]                     mtime_full;
   reg [32-1:0]                               mscratch;
   reg [32-1:0]                               mepc;
   reg [4-1:0]                           mecode;
   reg                                              mint;
   reg [32-1:0]                               mbadaddr;

   wire                                             ie;

   wire [32-1:0]                              mcpuid;
   wire [32-1:0]                              mimpid;
   wire [32-1:0]                              mhartid;
   wire [32-1:0]                              mstatus;
   wire [32-1:0]                              mtdeleg;
   wire [32-1:0]                              mip;
   wire [32-1:0]                              mcause;

   reg [32-1:0]                               to_host;
   reg [32-1:0]                               from_host;

   wire                                             mtimer_expired;

   wire                                             host_wen;
   wire                                             system_en;
   wire                                             system_wen;
   wire                                             wen_internal;
   wire                                             illegal_region;
   reg                                              defined;
   reg [32-1:0]                               wdata_internal;
   wire                                             uinterrupt;
   wire                                             minterrupt;
   reg [4-1:0]                           interrupt_code;

   wire                                             code_imem;


   wire [32-1:0]                              padded_prv = prv;
   assign handler_PC = mtvec + (padded_prv << 5);

   assign prv = priv_stack[2:1];
   assign ie = priv_stack[0];

   assign host_wen = (htif_state == HTIF_STATE_IDLE) && htif_pcr_req_valid && htif_pcr_req_rw;
   assign system_en = cmd[2];
   assign system_wen = cmd[1] || cmd[0];
   assign wen_internal = host_wen || system_wen;

   assign illegal_region = (system_wen && (addr[11:10] == 2'b11))
     || (system_en && addr[9:8] > prv);

   assign illegal_access = illegal_region || (system_en && !defined);

   always @(*) begin
      wdata_internal = wdata;
      if (host_wen) begin
         wdata_internal = htif_pcr_req_data;
      end else if (system_wen) begin
         case (cmd)
            6: wdata_internal = rdata | wdata;
            7: wdata_internal = rdata & ~wdata;
           default : wdata_internal = wdata;
         endcase // case (cmd)
      end
   end // always @ begin

   assign uinterrupt = 1'b0;
   assign minterrupt = |(mie & mip);
   assign interrupt_pending = |mip;

   always @(*) begin
      interrupt_code = 1;
      case (prv)
         0: interrupt_taken = (ie && uinterrupt) || minterrupt;
         3: interrupt_taken = (ie && minterrupt);
        default : interrupt_taken = 1'b1;
      endcase // case (prv)
   end

   always @(posedge clk) begin
      if (htif_reset)
        htif_state <= HTIF_STATE_IDLE;
      else
        htif_state <= next_htif_state;
      if (htif_fire)
        htif_resp_data <= htif_rdata;
   end

   always @(*) begin
      htif_fire = 1'b0;
      next_htif_state = htif_state;
      case (htif_state)
        HTIF_STATE_IDLE : begin
           if (htif_pcr_req_valid) begin
              htif_fire = 1'b1;
              next_htif_state = HTIF_STATE_WAIT;
           end
        end
        HTIF_STATE_WAIT : begin
           if (htif_pcr_resp_ready) begin
              next_htif_state = HTIF_STATE_IDLE;
           end
        end
      endcase // case (htif_state)
   end // always @ begin

   assign htif_pcr_req_ready = (htif_state == HTIF_STATE_IDLE);
   assign htif_pcr_resp_valid = (htif_state == HTIF_STATE_WAIT);
   assign htif_pcr_resp_data = htif_resp_data;

   assign mcpuid = ( 1<< 20) | ( 1<< 8); // 'I' and 'U' bits set
   assign mimpid = 32'h8000;
   assign mhartid = 0;

   always @(posedge clk) begin
      if (reset) begin
         priv_stack <= 6'b000110;
      end else if (wen_internal && addr == 12'h300) begin
         priv_stack <= wdata_internal[5:0];
      end else if (exception) begin
         // no delegation to U means all exceptions go to M
         priv_stack <= {priv_stack[2:0],2'b11,1'b0};
      end else if (eret) begin
         priv_stack <= {2'b00,1'b1,priv_stack[5:3]};
      end
   end // always @ (posedge clk)

   assign epc = mepc;

   // this implementation has SD, VM, MPRV, XS, and FS set to 0
   assign mstatus = {26'b0, priv_stack};

   assign mtdeleg = 0;

   assign mtimer_expired = (mtimecmp == mtime_full[0+:32]);

   always @(posedge clk) begin
      if (reset) begin
         mtip <= 0;
         msip <= 0;
      end else begin
         if (mtimer_expired)
           mtip <= 1;
         if (wen_internal && addr == 12'h321)
           mtip <= 0;
         if (wen_internal && addr == 12'h344) begin
            mtip <= wdata_internal[7];
            msip <= wdata_internal[3];
         end
      end // else: !if(reset)
   end // always @ (posedge clk)
   assign mip = {ext_interrupts,mtip,3'b0,msip,3'b0};


   always @(posedge clk) begin
      if (reset) begin
         mie <= 0;
      end else if (wen_internal && addr == 12'h304) begin
	 mie <= wdata_internal;
      end
   end // always @ (posedge clk)

   always @(posedge clk) begin
      if (interrupt_taken)
	mepc <= (exception_PC & {{30{1'b1}},2'b0}) + 32'h4;
      if (exception)
        mepc <= exception_PC & {{30{1'b1}},2'b0};
      if (wen_internal && addr == 12'h341)
        mepc <= wdata_internal & {{30{1'b1}},2'b0};
   end

   always @(posedge clk) begin
      if (reset) begin
         mecode <= 0;
         mint <= 0;
      end else if (wen_internal && addr == 12'h342) begin
         mecode <= wdata_internal[3:0];
         mint <= wdata_internal[31];
      end else begin
         if (interrupt_taken) begin
            mecode <= interrupt_code;
            mint <= 1'b1;
         end else if (exception) begin
            mecode <= exception_code;
            mint <= 1'b0;
         end
      end // else: !if(reset)
   end // always @ (posedge clk)
   assign mcause = {mint,27'b0,mecode};

   assign code_imem = (exception_code == 0)
     || (exception_code == 0);

   always @(posedge clk) begin
      if (exception)
        mbadaddr <= (code_imem) ? exception_PC : exception_load_addr;
      if (wen_internal && addr == 12'h343)
        mbadaddr <= wdata_internal;
   end

   always @(*) begin
      case (htif_pcr_req_addr)
         12'h780: htif_rdata = to_host;
         12'h781: htif_rdata = from_host;
        default : htif_rdata = 0;
      endcase // case (htif_pcr_req_addr)
   end // always @ begin

   always @(*) begin
      case (addr)
         12'hC00: begin rdata = cycle_full[0+:32]; defined = 1'b1; end
         12'hC01: begin rdata = time_full[0+:32]; defined = 1'b1; end
         12'hC02: begin rdata = instret_full[0+:32]; defined = 1'b1; end
         12'hC80: begin rdata = cycle_full[32+:32]; defined = 1'b1; end
         12'hC81: begin rdata = time_full[32+:32]; defined = 1'b1; end
         12'hC82: begin rdata = instret_full[32+:32]; defined = 1'b1; end
         12'hF00: begin rdata = mcpuid; defined = 1'b1; end
         12'hF01: begin rdata = mimpid; defined = 1'b1; end
         12'hF10: begin rdata = mhartid; defined = 1'b1; end
         12'h300: begin rdata = mstatus; defined = 1'b1; end
         12'h301: begin rdata = mtvec; defined = 1'b1; end
         12'h302: begin rdata = mtdeleg; defined = 1'b1; end
         12'h304: begin rdata = mie; defined = 1'b1; end
         12'h321: begin rdata = mtimecmp; defined = 1'b1; end
         12'h701: begin rdata = mtime_full[0+:32]; defined = 1'b1; end
         12'h741: begin rdata = mtime_full[32+:32]; defined = 1'b1; end
         12'h340: begin rdata = mscratch; defined = 1'b1; end
         12'h341: begin rdata = mepc; defined = 1'b1; end
         12'h342: begin rdata = mcause; defined = 1'b1; end
         12'h343: begin rdata = mbadaddr; defined = 1'b1; end
         12'h344: begin rdata = mip; defined = 1'b1; end
         12'h900: begin rdata = cycle_full[0+:32]; defined = 1'b1; end
         12'h901: begin rdata = time_full[0+:32]; defined = 1'b1; end
         12'h902: begin rdata = instret_full[0+:32]; defined = 1'b1; end
         12'h980: begin rdata = cycle_full[32+:32]; defined = 1'b1; end
         12'h981: begin rdata = time_full[32+:32]; defined = 1'b1; end
         12'h982: begin rdata = instret_full[32+:32]; defined = 1'b1; end
        // non-standard
         12'h780: begin rdata = to_host; defined = 1'b1; end
         12'h781: begin rdata = from_host; defined = 1'b1; end
        default : begin rdata = 0; defined = 1'b0; end
      endcase // case (addr)
   end // always @ (*)


   always @(posedge clk) begin
      if (reset) begin
         cycle_full <= 0;
         time_full <= 0;
         instret_full <= 0;
         mtime_full <= 0;
         to_host <= 0;
         from_host <= 0;
         mtvec <= 'h100;
         mtimecmp <= 0;
         mscratch <= 0;
      end else begin
         cycle_full <= cycle_full + 1;
         time_full <= time_full + 1;
         if (retire)
           instret_full <= instret_full + 1;
         mtime_full <= mtime_full + 1;
         if (wen_internal) begin
            case (addr)
               12'hC00: cycle_full[0+:32] <= wdata_internal;
               12'hC01: time_full[0+:32] <= wdata_internal;
               12'hC02: instret_full[0+:32] <= wdata_internal;
               12'hC80: cycle_full[32+:32] <= wdata_internal;
               12'hC81: time_full[32+:32] <= wdata_internal;
               12'hC82: instret_full[32+:32] <= wdata_internal;
              // mcpuid is read-only
              // mimpid is read-only
              // mhartid is read-only
              // mstatus handled separately
               12'h301: mtvec <= wdata_internal & {{30{1'b1}},2'b0};
              // mtdeleg constant
              // mie handled separately
               12'h321: mtimecmp <= wdata_internal;
               12'h701: mtime_full[0+:32] <= wdata_internal;
               12'h741: mtime_full[32+:32] <= wdata_internal;
               12'h340: mscratch <= wdata_internal;
              // mepc handled separately
              // mcause handled separately
              // mbadaddr handled separately
              // mip handled separately
               12'h900: cycle_full[0+:32] <= wdata_internal;
               12'h901: time_full[0+:32] <= wdata_internal;
               12'h902: instret_full[0+:32] <= wdata_internal;
               12'h980: cycle_full[32+:32] <= wdata_internal;
               12'h981: time_full[32+:32] <= wdata_internal;
               12'h982: instret_full[32+:32] <= wdata_internal;
               12'h780: to_host <= wdata_internal;
               12'h781: from_host <= wdata_internal;
              default : ;
            endcase // case (addr)
         end // if (wen_internal)
         if (htif_fire && htif_pcr_req_addr ==  12'h780&& !system_wen) begin
            to_host <= 0;
         end
      end // else: !if(reset)
   end // always @ (posedge clk)



endmodule // vscale_csr_file
