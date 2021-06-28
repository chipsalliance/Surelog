package riscv;

    // ----------------------
    // Data and Address length
    // ----------------------
    typedef enum logic [3:0] {
       ModeOff  = 0,
       ModeSv32 = 1,
       ModeSv39 = 8,
       ModeSv48 = 9,
       ModeSv57 = 10,
       ModeSv64 = 11
    } vm_mode_t;

    localparam XLEN = 64;

    // Warning: When using STD_CACHE, configuration must be PLEN=56 and VLEN=64
    // Warning: VLEN must be superior or equal to PLEN
    localparam VLEN       = (XLEN == 32) ? 32 : 64;    // virtual address length
    localparam PLEN       = (XLEN == 32) ? 32 : 56;    // physical address length

    localparam IS_XLEN64  = (XLEN == 32) ? 1'b0 : 1'b1;
    localparam ModeW      = (XLEN == 32) ? 1 : 4;
    localparam ASIDW      = (XLEN == 32) ? 9 : 16;
    localparam PPNW       = (XLEN == 32) ? 22 : 44;
    localparam vm_mode_t MODE_SV = (XLEN == 32) ? ModeSv32 : ModeSv39;
    localparam SV         = (MODE_SV == ModeSv32) ? 32 : 39;
    localparam VPN2       = (VLEN-31 < 8) ? VLEN-31 : 8;

    typedef logic [XLEN-1:0] xlen_t;

    // --------------------
    // Privilege Spec
    // --------------------
    typedef enum logic[1:0] {
      PRIV_LVL_M = 2'b11,
      PRIV_LVL_S = 2'b01,
      PRIV_LVL_U = 2'b00
    } priv_lvl_t;

    // type which holds xlen
    typedef enum logic [1:0] {
        XLEN_32  = 2'b01,
        XLEN_64  = 2'b10,
        XLEN_128 = 2'b11
    } xlen_e;

    typedef enum logic [1:0] {
        Off     = 2'b00,
        Initial = 2'b01,
        Clean   = 2'b10,
        Dirty   = 2'b11
    } xs_t;

    typedef struct packed {
        logic         sd;     // signal dirty state - read-only
        logic [62:36] wpri4;  // writes preserved reads ignored
        xlen_e        sxl;    // variable supervisor mode xlen - hardwired to zero
        xlen_e        uxl;    // variable user mode xlen - hardwired to zero
        logic [8:0]   wpri3;  // writes preserved reads ignored
        logic         tsr;    // trap sret
        logic         tw;     // time wait
        logic         tvm;    // trap virtual memory
        logic         mxr;    // make executable readable
        logic         sum;    // permit supervisor user memory access
        logic         mprv;   // modify privilege - privilege level for ld/st
        xs_t          xs;     // extension register - hardwired to zero
        xs_t          fs;     // floating point extension register
        priv_lvl_t    mpp;    // holds the previous privilege mode up to machine
        logic [1:0]   wpri2;  // writes preserved reads ignored
        logic         spp;    // holds the previous privilege mode up to supervisor
        logic         mpie;   // machine interrupts enable bit active prior to trap
        logic         wpri1;  // writes preserved reads ignored
        logic         spie;   // supervisor interrupts enable bit active prior to trap
        logic         upie;   // user interrupts enable bit active prior to trap - hardwired to zero
        logic         mie;    // machine interrupts enable
        logic         wpri0;  // writes preserved reads ignored
        logic         sie;    // supervisor interrupts enable
        logic         uie;    // user interrupts enable - hardwired to zero
    } status_rv_t;

    typedef struct packed {
        logic [ModeW-1:0] mode;
        logic [ASIDW-1:0] asid;
        logic [PPNW-1:0]  ppn;
    } satp_t;

    // --------------------
    // Instruction Types
    // --------------------
    typedef struct packed {
        logic [31:25] funct7;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } rtype_t;

    typedef struct packed {
        logic [31:27] rs3;
        logic [26:25] funct2;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } r4type_t;

    typedef struct packed {
        logic [31:27] funct5;
        logic [26:25] fmt;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] rm;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } rftype_t; // floating-point

    typedef struct packed {
        logic [31:30] funct2;
        logic [29:25] vecfltop;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:14] repl;
        logic [13:12] vfmt;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } rvftype_t; // vectorial floating-point

    typedef struct packed {
        logic [31:20] imm;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } itype_t;

    typedef struct packed {
        logic [31:25] imm;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  imm0;
        logic [6:0]   opcode;
    } stype_t;

    typedef struct packed {
        logic [31:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } utype_t;

    // atomic instructions
    typedef struct packed {
        logic [31:27] funct5;
        logic         aq;
        logic         rl;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } atype_t;

    typedef union packed {
        logic [31:0]   instr;
        rtype_t        rtype;
        r4type_t       r4type;
        rftype_t       rftype;
        rvftype_t      rvftype;
        itype_t        itype;
        stype_t        stype;
        utype_t        utype;
        atype_t        atype;
    } instruction_t;

    // --------------------
    // Opcodes
    // --------------------
    // RV32/64G listings:
    // Quadrant 0
    localparam OpcodeLoad      = 7'b00_000_11;
    localparam OpcodeLoadFp    = 7'b00_001_11;
    localparam OpcodeCustom0   = 7'b00_010_11;
    localparam OpcodeMiscMem   = 7'b00_011_11;
    localparam OpcodeOpImm     = 7'b00_100_11;
    localparam OpcodeAuipc     = 7'b00_101_11;
    localparam OpcodeOpImm32   = 7'b00_110_11;
    // Quadrant 1
    localparam OpcodeStore     = 7'b01_000_11;
    localparam OpcodeStoreFp   = 7'b01_001_11;
    localparam OpcodeCustom1   = 7'b01_010_11;
    localparam OpcodeAmo       = 7'b01_011_11;
    localparam OpcodeOp        = 7'b01_100_11;
    localparam OpcodeLui       = 7'b01_101_11;
    localparam OpcodeOp32      = 7'b01_110_11;
    // Quadrant 2
    localparam OpcodeMadd      = 7'b10_000_11;
    localparam OpcodeMsub      = 7'b10_001_11;
    localparam OpcodeNmsub     = 7'b10_010_11;
    localparam OpcodeNmadd     = 7'b10_011_11;
    localparam OpcodeOpFp      = 7'b10_100_11;
    localparam OpcodeRsrvd1    = 7'b10_101_11;
    localparam OpcodeCustom2   = 7'b10_110_11;
    // Quadrant 3
    localparam OpcodeBranch    = 7'b11_000_11;
    localparam OpcodeJalr      = 7'b11_001_11;
    localparam OpcodeRsrvd2    = 7'b11_010_11;
    localparam OpcodeJal       = 7'b11_011_11;
    localparam OpcodeSystem    = 7'b11_100_11;
    localparam OpcodeRsrvd3    = 7'b11_101_11;
    localparam OpcodeCustom3   = 7'b11_110_11;

    // RV64C/RV32C listings:
    // Quadrant 0
    localparam OpcodeC0             = 2'b00;
    localparam OpcodeC0Addi4spn     = 3'b000;
    localparam OpcodeC0Fld          = 3'b001;
    localparam OpcodeC0Lw           = 3'b010;
    localparam OpcodeC0Ld           = 3'b011;
    localparam OpcodeC0Rsrvd        = 3'b100;
    localparam OpcodeC0Fsd          = 3'b101;
    localparam OpcodeC0Sw           = 3'b110;
    localparam OpcodeC0Sd           = 3'b111;
    // Quadrant 1
    localparam OpcodeC1             = 2'b01;
    localparam OpcodeC1Addi         = 3'b000;
    localparam OpcodeC1Addiw        = 3'b001; //for RV64I only
    localparam OpcodeC1Jal          = 3'b001; //for RV32I only
    localparam OpcodeC1Li           = 3'b010;
    localparam OpcodeC1LuiAddi16sp  = 3'b011;
    localparam OpcodeC1MiscAlu      = 3'b100;
    localparam OpcodeC1J            = 3'b101;
    localparam OpcodeC1Beqz         = 3'b110;
    localparam OpcodeC1Bnez         = 3'b111;
    // Quadrant 2
    localparam OpcodeC2             = 2'b10;
    localparam OpcodeC2Slli         = 3'b000;
    localparam OpcodeC2Fldsp        = 3'b001;
    localparam OpcodeC2Lwsp         = 3'b010;
    localparam OpcodeC2Ldsp         = 3'b011;
    localparam OpcodeC2JalrMvAdd    = 3'b100;
    localparam OpcodeC2Fsdsp        = 3'b101;
    localparam OpcodeC2Swsp         = 3'b110;
    localparam OpcodeC2Sdsp         = 3'b111;

    // ----------------------
    // Virtual Memory
    // ----------------------
    // memory management, pte
    typedef struct packed {
        logic [9:0]  reserved;
        logic [PLEN-12-1:0] ppn;
        logic [1:0]  rsw;
        logic d;
        logic a;
        logic g;
        logic u;
        logic x;
        logic w;
        logic r;
        logic v;
    } pte_t;

    // ----------------------
    // Exception Cause Codes
    // ----------------------
    localparam logic [XLEN-1:0] INSTR_ADDR_MISALIGNED = 0;
    localparam logic [XLEN-1:0] INSTR_ACCESS_FAULT    = 1;  // Illegal access as governed by PMPs and PMAs
    localparam logic [XLEN-1:0] ILLEGAL_INSTR         = 2;
    localparam logic [XLEN-1:0] BREAKPOINT            = 3;
    localparam logic [XLEN-1:0] LD_ADDR_MISALIGNED    = 4;
    localparam logic [XLEN-1:0] LD_ACCESS_FAULT       = 5;  // Illegal access as governed by PMPs and PMAs
    localparam logic [XLEN-1:0] ST_ADDR_MISALIGNED    = 6;
    localparam logic [XLEN-1:0] ST_ACCESS_FAULT       = 7;  // Illegal access as governed by PMPs and PMAs
    localparam logic [XLEN-1:0] ENV_CALL_UMODE        = 8;  // environment call from user mode
    localparam logic [XLEN-1:0] ENV_CALL_SMODE        = 9;  // environment call from supervisor mode
    localparam logic [XLEN-1:0] ENV_CALL_MMODE        = 11; // environment call from machine mode
    localparam logic [XLEN-1:0] INSTR_PAGE_FAULT      = 12; // Instruction page fault
    localparam logic [XLEN-1:0] LOAD_PAGE_FAULT       = 13; // Load page fault
    localparam logic [XLEN-1:0] STORE_PAGE_FAULT      = 15; // Store page fault
    localparam logic [XLEN-1:0] DEBUG_REQUEST         = 24; // Debug request

    localparam int unsigned IRQ_S_SOFT  = 1;
    localparam int unsigned IRQ_M_SOFT  = 3;
    localparam int unsigned IRQ_S_TIMER = 5;
    localparam int unsigned IRQ_M_TIMER = 7;
    localparam int unsigned IRQ_S_EXT   = 9;
    localparam int unsigned IRQ_M_EXT   = 11;

    localparam logic [XLEN-1:0] MIP_SSIP = 1 << IRQ_S_SOFT;
    localparam logic [XLEN-1:0] MIP_MSIP = 1 << IRQ_M_SOFT;
    localparam logic [XLEN-1:0] MIP_STIP = 1 << IRQ_S_TIMER;
    localparam logic [XLEN-1:0] MIP_MTIP = 1 << IRQ_M_TIMER;
    localparam logic [XLEN-1:0] MIP_SEIP = 1 << IRQ_S_EXT;
    localparam logic [XLEN-1:0] MIP_MEIP = 1 << IRQ_M_EXT;

    localparam logic [XLEN-1:0] S_SW_INTERRUPT    = (1 << (XLEN-1)) | IRQ_S_SOFT;
    localparam logic [XLEN-1:0] M_SW_INTERRUPT    = (1 << (XLEN-1)) | IRQ_M_SOFT;
    localparam logic [XLEN-1:0] S_TIMER_INTERRUPT = (1 << (XLEN-1)) | IRQ_S_TIMER;
    localparam logic [XLEN-1:0] M_TIMER_INTERRUPT = (1 << (XLEN-1)) | IRQ_M_TIMER;
    localparam logic [XLEN-1:0] S_EXT_INTERRUPT   = (1 << (XLEN-1)) | IRQ_S_EXT;
    localparam logic [XLEN-1:0] M_EXT_INTERRUPT   = (1 << (XLEN-1)) | IRQ_M_EXT;

    // -----
    // CSRs
    // -----
    typedef enum logic [11:0] {
        // Floating-Point CSRs
        CSR_FFLAGS         = 12'h001,
        CSR_FRM            = 12'h002,
        CSR_FCSR           = 12'h003,
        CSR_FTRAN          = 12'h800,
        // Supervisor Mode CSRs
        CSR_SSTATUS        = 12'h100,
        CSR_SIE            = 12'h104,
        CSR_STVEC          = 12'h105,
        CSR_SCOUNTEREN     = 12'h106,
        CSR_SSCRATCH       = 12'h140,
        CSR_SEPC           = 12'h141,
        CSR_SCAUSE         = 12'h142,
        CSR_STVAL          = 12'h143,
        CSR_SIP            = 12'h144,
        CSR_SATP           = 12'h180,
        // Machine Mode CSRs
        CSR_MSTATUS        = 12'h300,
        CSR_MISA           = 12'h301,
        CSR_MEDELEG        = 12'h302,
        CSR_MIDELEG        = 12'h303,
        CSR_MIE            = 12'h304,
        CSR_MTVEC          = 12'h305,
        CSR_MCOUNTEREN     = 12'h306,
        CSR_MSCRATCH       = 12'h340,
        CSR_MEPC           = 12'h341,
        CSR_MCAUSE         = 12'h342,
        CSR_MTVAL          = 12'h343,
        CSR_MIP            = 12'h344,
        CSR_PMPCFG0        = 12'h3A0,
        CSR_PMPCFG1        = 12'h3A1,
        CSR_PMPCFG2        = 12'h3A2,
        CSR_PMPCFG3        = 12'h3A3,
        CSR_PMPADDR0       = 12'h3B0,
        CSR_PMPADDR1       = 12'h3B1,
        CSR_PMPADDR2       = 12'h3B2,
        CSR_PMPADDR3       = 12'h3B3,
        CSR_PMPADDR4       = 12'h3B4,
        CSR_PMPADDR5       = 12'h3B5,
        CSR_PMPADDR6       = 12'h3B6,
        CSR_PMPADDR7       = 12'h3B7,
        CSR_PMPADDR8       = 12'h3B8,
        CSR_PMPADDR9       = 12'h3B9,
        CSR_PMPADDR10      = 12'h3BA,
        CSR_PMPADDR11      = 12'h3BB,
        CSR_PMPADDR12      = 12'h3BC,
        CSR_PMPADDR13      = 12'h3BD,
        CSR_PMPADDR14      = 12'h3BE,
        CSR_PMPADDR15      = 12'h3BF,
        CSR_MVENDORID      = 12'hF11,
        CSR_MARCHID        = 12'hF12,
        CSR_MIMPID         = 12'hF13,
        CSR_MHARTID        = 12'hF14,
        CSR_MCYCLE         = 12'hB00,
        CSR_MINSTRET       = 12'hB02,
        // Performance counters (Machine Mode)
        CSR_ML1_ICACHE_MISS = 12'hB03,  // L1 Instr Cache Miss
        CSR_ML1_DCACHE_MISS = 12'hB04,  // L1 Data Cache Miss
        CSR_MITLB_MISS      = 12'hB05,  // ITLB Miss
        CSR_MDTLB_MISS      = 12'hB06,  // DTLB Miss
        CSR_MLOAD           = 12'hB07,  // Loads
        CSR_MSTORE          = 12'hB08,  // Stores
        CSR_MEXCEPTION      = 12'hB09,  // Taken exceptions
        CSR_MEXCEPTION_RET  = 12'hB0A,  // Exception return
        CSR_MBRANCH_JUMP    = 12'hB0B,  // Software change of PC
        CSR_MCALL           = 12'hB0C,  // Procedure call
        CSR_MRET            = 12'hB0D,  // Procedure Return
        CSR_MMIS_PREDICT    = 12'hB0E,  // Branch mis-predicted
        CSR_MSB_FULL        = 12'hB0F,  // Scoreboard full
        CSR_MIF_EMPTY       = 12'hB10,  // instruction fetch queue empty
        CSR_MHPM_COUNTER_17 = 12'hB11,  // reserved
        CSR_MHPM_COUNTER_18 = 12'hB12,  // reserved
        CSR_MHPM_COUNTER_19 = 12'hB13,  // reserved
        CSR_MHPM_COUNTER_20 = 12'hB14,  // reserved
        CSR_MHPM_COUNTER_21 = 12'hB15,  // reserved
        CSR_MHPM_COUNTER_22 = 12'hB16,  // reserved
        CSR_MHPM_COUNTER_23 = 12'hB17,  // reserved
        CSR_MHPM_COUNTER_24 = 12'hB18,  // reserved
        CSR_MHPM_COUNTER_25 = 12'hB19,  // reserved
        CSR_MHPM_COUNTER_26 = 12'hB1A,  // reserved
        CSR_MHPM_COUNTER_27 = 12'hB1B,  // reserved
        CSR_MHPM_COUNTER_28 = 12'hB1C,  // reserved
        CSR_MHPM_COUNTER_29 = 12'hB1D,  // reserved
        CSR_MHPM_COUNTER_30 = 12'hB1E,  // reserved
        CSR_MHPM_COUNTER_31 = 12'hB1F,  // reserved
        // Cache Control (platform specifc)
        CSR_DCACHE         = 12'h701,
        CSR_ICACHE         = 12'h700,
        // Triggers
        CSR_TSELECT        = 12'h7A0,
        CSR_TDATA1         = 12'h7A1,
        CSR_TDATA2         = 12'h7A2,
        CSR_TDATA3         = 12'h7A3,
        CSR_TINFO          = 12'h7A4,
        // Debug CSR
        CSR_DCSR           = 12'h7b0,
        CSR_DPC            = 12'h7b1,
        CSR_DSCRATCH0      = 12'h7b2, // optional
        CSR_DSCRATCH1      = 12'h7b3, // optional
        // Counters and Timers (User Mode - R/O Shadows)
        CSR_CYCLE          = 12'hC00,
        CSR_TIME           = 12'hC01,
        CSR_INSTRET        = 12'hC02,
        // Performance counters (User Mode - R/O Shadows)
        CSR_L1_ICACHE_MISS = 12'hC03,  // L1 Instr Cache Miss
        CSR_L1_DCACHE_MISS = 12'hC04,  // L1 Data Cache Miss
        CSR_ITLB_MISS      = 12'hC05,  // ITLB Miss
        CSR_DTLB_MISS      = 12'hC06,  // DTLB Miss
        CSR_LOAD           = 12'hC07,  // Loads
        CSR_STORE          = 12'hC08,  // Stores
        CSR_EXCEPTION      = 12'hC09,  // Taken exceptions
        CSR_EXCEPTION_RET  = 12'hC0A,  // Exception return
        CSR_BRANCH_JUMP    = 12'hC0B,  // Software change of PC
        CSR_CALL           = 12'hC0C,  // Procedure call
        CSR_RET            = 12'hC0D,  // Procedure Return
        CSR_MIS_PREDICT    = 12'hC0E,  // Branch mis-predicted
        CSR_SB_FULL        = 12'hC0F,  // Scoreboard full
        CSR_IF_EMPTY       = 12'hC10,  // instruction fetch queue empty
        CSR_HPM_COUNTER_17 = 12'hC11,  // reserved
        CSR_HPM_COUNTER_18 = 12'hC12,  // reserved
        CSR_HPM_COUNTER_19 = 12'hC13,  // reserved
        CSR_HPM_COUNTER_20 = 12'hC14,  // reserved
        CSR_HPM_COUNTER_21 = 12'hC15,  // reserved
        CSR_HPM_COUNTER_22 = 12'hC16,  // reserved
        CSR_HPM_COUNTER_23 = 12'hC17,  // reserved
        CSR_HPM_COUNTER_24 = 12'hC18,  // reserved
        CSR_HPM_COUNTER_25 = 12'hC19,  // reserved
        CSR_HPM_COUNTER_26 = 12'hC1A,  // reserved
        CSR_HPM_COUNTER_27 = 12'hC1B,  // reserved
        CSR_HPM_COUNTER_28 = 12'hC1C,  // reserved
        CSR_HPM_COUNTER_29 = 12'hC1D,  // reserved
        CSR_HPM_COUNTER_30 = 12'hC1E,  // reserved
        CSR_HPM_COUNTER_31 = 12'hC1F  // reserved
    } csr_reg_t;

    localparam logic [63:0] SSTATUS_UIE  = 'h00000001;
    localparam logic [63:0] SSTATUS_SIE  = 'h00000002;
    localparam logic [63:0] SSTATUS_SPIE = 'h00000020;
    localparam logic [63:0] SSTATUS_SPP  = 'h00000100;
    localparam logic [63:0] SSTATUS_FS   = 'h00006000;
    localparam logic [63:0] SSTATUS_XS   = 'h00018000;
    localparam logic [63:0] SSTATUS_SUM  = 'h00040000;
    localparam logic [63:0] SSTATUS_MXR  = 'h00080000;
    localparam logic [63:0] SSTATUS_UPIE = 'h00000010;
    localparam logic [63:0] SSTATUS_UXL  = 64'h0000000300000000;
    localparam logic [63:0] SSTATUS_SD   = {IS_XLEN64, 31'h00000000, ~IS_XLEN64, 31'h00000000};

    localparam logic [63:0] MSTATUS_UIE  = 'h00000001;
    localparam logic [63:0] MSTATUS_SIE  = 'h00000002;
    localparam logic [63:0] MSTATUS_HIE  = 'h00000004;
    localparam logic [63:0] MSTATUS_MIE  = 'h00000008;
    localparam logic [63:0] MSTATUS_UPIE = 'h00000010;
    localparam logic [63:0] MSTATUS_SPIE = 'h00000020;
    localparam logic [63:0] MSTATUS_HPIE = 'h00000040;
    localparam logic [63:0] MSTATUS_MPIE = 'h00000080;
    localparam logic [63:0] MSTATUS_SPP  = 'h00000100;
    localparam logic [63:0] MSTATUS_HPP  = 'h00000600;
    localparam logic [63:0] MSTATUS_MPP  = 'h00001800;
    localparam logic [63:0] MSTATUS_FS   = 'h00006000;
    localparam logic [63:0] MSTATUS_XS   = 'h00018000;
    localparam logic [63:0] MSTATUS_MPRV = 'h00020000;
    localparam logic [63:0] MSTATUS_SUM  = 'h00040000;
    localparam logic [63:0] MSTATUS_MXR  = 'h00080000;
    localparam logic [63:0] MSTATUS_TVM  = 'h00100000;
    localparam logic [63:0] MSTATUS_TW   = 'h00200000;
    localparam logic [63:0] MSTATUS_TSR  = 'h00400000;
    localparam logic [63:0] MSTATUS_UXL  = {30'h0000000, IS_XLEN64, IS_XLEN64, 32'h00000000};
    localparam logic [63:0] MSTATUS_SXL  = {28'h0000000, IS_XLEN64, IS_XLEN64, 34'h00000000};
    localparam logic [63:0] MSTATUS_SD   = {IS_XLEN64, 31'h00000000, ~IS_XLEN64, 31'h00000000};

    typedef enum logic [2:0] {
        CSRRW  = 3'h1,
        CSRRS  = 3'h2,
        CSRRC  = 3'h3,
        CSRRWI = 3'h5,
        CSRRSI = 3'h6,
        CSRRCI = 3'h7
    } csr_op_t;

    // decoded CSR address
    typedef struct packed {
        logic [1:0]  rw;
        priv_lvl_t   priv_lvl;
        logic  [7:0] address;
    } csr_addr_t;

    typedef union packed {
        csr_reg_t   address;
        csr_addr_t  csr_decode;
    } csr_t;

    // Floating-Point control and status register (32-bit!)
    typedef struct packed {
        logic [31:15] reserved;  // reserved for L extension, return 0 otherwise
        logic [6:0]   fprec;     // div/sqrt precision control
        logic [2:0]   frm;       // float rounding mode
        logic [4:0]   fflags;    // float exception flags
    } fcsr_t;

    // PMP
    typedef enum logic [1:0] {
        OFF   = 2'b00,
        TOR   = 2'b01,
        NA4   = 2'b10,
        NAPOT = 2'b11
    } pmp_addr_mode_t;

    // PMP Access Type
    typedef enum logic [2:0] {
        ACCESS_NONE  = 3'b000,
        ACCESS_READ  = 3'b001,
        ACCESS_WRITE = 3'b010,
        ACCESS_EXEC  = 3'b100
    } pmp_access_t;

    typedef struct packed {
        logic           x;
        logic           w;
        logic           r;
    } pmpcfg_access_t;

    // packed struct of a PMP configuration register (8bit)
    typedef struct packed {
        logic           locked;     // lock this configuration
        logic [1:0]     reserved;
        pmp_addr_mode_t addr_mode;  // Off, TOR, NA4, NAPOT
        pmpcfg_access_t access_type;
    } pmpcfg_t;

    // -----
    // Debug
    // -----
    typedef struct packed {
        logic [31:28]     xdebugver;
        logic [27:16]     zero2;
        logic             ebreakm;
        logic             zero1;
        logic             ebreaks;
        logic             ebreaku;
        logic             stepie;
        logic             stopcount;
        logic             stoptime;
        logic [8:6]       cause;
        logic             zero0;
        logic             mprven;
        logic             nmip;
        logic             step;
        priv_lvl_t        prv;
    } dcsr_t;

    // Instruction Generation *incomplete*
    function automatic logic [31:0] jal (logic[4:0] rd, logic [20:0] imm);
        // OpCode Jal
        return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'h6f};
    endfunction

    function automatic logic [31:0] jalr (logic[4:0] rd, logic[4:0] rs1, logic [11:0] offset);
        // OpCode Jal
        return {offset[11:0], rs1, 3'b0, rd, 7'h67};
    endfunction

    function automatic logic [31:0] andi (logic[4:0] rd, logic[4:0] rs1, logic [11:0] imm);
        // OpCode andi
        return {imm[11:0], rs1, 3'h7, rd, 7'h13};
    endfunction

    function automatic logic [31:0] slli (logic[4:0] rd, logic[4:0] rs1, logic [5:0] shamt);
        // OpCode slli
        return {6'b0, shamt[5:0], rs1, 3'h1, rd, 7'h13};
    endfunction

    function automatic logic [31:0] srli (logic[4:0] rd, logic[4:0] rs1, logic [5:0] shamt);
        // OpCode srli
        return {6'b0, shamt[5:0], rs1, 3'h5, rd, 7'h13};
    endfunction

    function automatic logic [31:0] load (logic [2:0] size, logic[4:0] dest, logic[4:0] base, logic [11:0] offset);
        // OpCode Load
        return {offset[11:0], base, size, dest, 7'h03};
    endfunction

    function automatic logic [31:0] auipc (logic[4:0] rd, logic [20:0] imm);
        // OpCode Auipc
        return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'h17};
    endfunction

    function automatic logic [31:0] store (logic [2:0] size, logic[4:0] src, logic[4:0] base, logic [11:0] offset);
        // OpCode Store
        return {offset[11:5], src, base, size, offset[4:0], 7'h23};
    endfunction

    function automatic logic [31:0] float_load (logic [2:0] size, logic[4:0] dest, logic[4:0] base, logic [11:0] offset);
        // OpCode Load
        return {offset[11:0], base, size, dest, 7'b00_001_11};
    endfunction

    function automatic logic [31:0] float_store (logic [2:0] size, logic[4:0] src, logic[4:0] base, logic [11:0] offset);
        // OpCode Store
        return {offset[11:5], src, base, size, offset[4:0], 7'b01_001_11};
    endfunction

    function automatic logic [31:0] csrw (csr_reg_t csr, logic[4:0] rs1);
                         // CSRRW, rd, OpCode System
        return {csr, rs1, 3'h1, 5'h0, 7'h73};
    endfunction

    function automatic logic [31:0] csrr (csr_reg_t csr, logic [4:0] dest);
                  // rs1, CSRRS, rd, OpCode System
        return {csr, 5'h0, 3'h2, dest, 7'h73};
    endfunction

    function automatic logic [31:0] ebreak ();
        return 32'h00100073;
    endfunction

    function automatic logic [31:0] nop ();
        return 32'h00000013;
    endfunction

    function automatic logic [31:0] illegal ();
        return 32'h00000000;
    endfunction


    // trace log compatible to spikes commit log feature
    // pragma translate_off
    function string spikeCommitLog(logic [63:0] pc, priv_lvl_t priv_lvl, logic [31:0] instr, logic [4:0] rd, logic [63:0] result, logic rd_fpr);
        string rd_s;
        string instr_word;

        automatic string rf_s = rd_fpr ? "f" : "x";

        if (instr[1:0] != 2'b11) begin
          instr_word = $sformatf("(0x%h)", instr[15:0]);
        end else begin
          instr_word = $sformatf("(0x%h)", instr);
        end

        if (rd < 10) rd_s = $sformatf("%s %0d", rf_s, rd);
        else rd_s = $sformatf("%s%0d", rf_s, rd);

        if (rd_fpr || rd != 0) begin
            // 0 0x0000000080000118 (0xeecf8f93) x31 0x0000000080004000
            return $sformatf("%d 0x%h %s %s 0x%h\n", priv_lvl, pc, instr_word, rd_s, result);
        end else begin
            // 0 0x000000008000019c (0x0040006f)
            return $sformatf("%d 0x%h %s\n", priv_lvl, pc, instr_word);
        end
    endfunction

    typedef struct {
        byte priv;
        longint unsigned pc;
        byte is_fp;
        byte rd;
        longint unsigned data;
        int unsigned instr;
        byte was_exception;
    } commit_log_t;
    // pragma translate_on

endpackage


package ariane_pkg;

    // ---------------
    // Global Config
    // ---------------
    // This is the new user config interface system. If you need to parameterize something
    // within Ariane add a field here and assign a default value to the config. Please make
    // sure to add a propper parameter check to the `check_cfg` function.
    localparam NrMaxRules = 16;

    typedef struct packed {
      int                               RASDepth;
      int                               BTBEntries;
      int                               BHTEntries;
      // PMAs
      int unsigned                      NrNonIdempotentRules;  // Number of non idempotent rules
      logic [NrMaxRules-1:0][63:0]      NonIdempotentAddrBase; // base which needs to match
      logic [NrMaxRules-1:0][63:0]      NonIdempotentLength;   // bit mask which bits to consider when matching the rule
      int unsigned                      NrExecuteRegionRules;  // Number of regions which have execute property
      logic [NrMaxRules-1:0][63:0]      ExecuteRegionAddrBase; // base which needs to match
      logic [NrMaxRules-1:0][63:0]      ExecuteRegionLength;   // bit mask which bits to consider when matching the rule
      int unsigned                      NrCachedRegionRules;   // Number of regions which have cached property
      logic [NrMaxRules-1:0][63:0]      CachedRegionAddrBase;  // base which needs to match
      logic [NrMaxRules-1:0][63:0]      CachedRegionLength;    // bit mask which bits to consider when matching the rule
      // cache config
      bit                               Axi64BitCompliant;     // set to 1 when using in conjunction with 64bit AXI bus adapter
      bit                               SwapEndianess;         // set to 1 to swap endianess inside L1.5 openpiton adapter
      //
      logic [63:0]                      DmBaseAddress;         // offset of the debug module
      int unsigned                      NrPMPEntries;          // Number of PMP entries
    } ariane_cfg_t;

    localparam ariane_cfg_t ArianeDefaultConfig = '{
      RASDepth: 2,
      BTBEntries: 32,
      BHTEntries: 128,
      // idempotent region
      NrNonIdempotentRules: 2,
      NonIdempotentAddrBase: {64'b0, 64'b0},
      NonIdempotentLength:   {64'b0, 64'b0},
      NrExecuteRegionRules: 3,
      //                      DRAM,          Boot ROM,   Debug Module
      ExecuteRegionAddrBase: {64'h8000_0000, 64'h1_0000, 64'h0},
      ExecuteRegionLength:   {64'h40000000,  64'h10000,  64'h1000},
      // cached region
      NrCachedRegionRules:    1,
      CachedRegionAddrBase:  {64'h8000_0000},
      CachedRegionLength:    {64'h40000000},
      //  cache config
      Axi64BitCompliant:      1'b1,
      SwapEndianess:          1'b0,
      // debug
      DmBaseAddress:          64'h0,
      NrPMPEntries:           8
    };

    // Function being called to check parameters
    function automatic void check_cfg (ariane_cfg_t Cfg);
      // pragma translate_off
      `ifndef VERILATOR
        assert(Cfg.RASDepth > 0);
        assert(2**$clog2(Cfg.BTBEntries)  == Cfg.BTBEntries);
        assert(2**$clog2(Cfg.BHTEntries)  == Cfg.BHTEntries);
        assert(Cfg.NrNonIdempotentRules <= NrMaxRules);
        assert(Cfg.NrExecuteRegionRules <= NrMaxRules);
        assert(Cfg.NrCachedRegionRules  <= NrMaxRules);
        assert(Cfg.NrPMPEntries <= 16);
      `endif
      // pragma translate_on
    endfunction

    function automatic logic range_check(logic[63:0] base, logic[63:0] len, logic[63:0] address);
      // if len is a power of two, and base is properly aligned, this check could be simplified
      return (address >= base) && (address < (base+len));
    endfunction : range_check

    function automatic logic is_inside_nonidempotent_regions (ariane_cfg_t Cfg, logic[63:0] address);
      logic[NrMaxRules-1:0] pass;
      pass = '0;
      for (int unsigned k = 0; k < Cfg.NrNonIdempotentRules; k++) begin
        pass[k] = range_check(Cfg.NonIdempotentAddrBase[k], Cfg.NonIdempotentLength[k], address);
      end
      return |pass;
    endfunction : is_inside_nonidempotent_regions

    function automatic logic is_inside_execute_regions (ariane_cfg_t Cfg, logic[63:0] address);
      // if we don't specify any region we assume everything is accessible
      logic[NrMaxRules-1:0] pass;
      pass = '0;
      for (int unsigned k = 0; k < Cfg.NrExecuteRegionRules; k++) begin
        pass[k] = range_check(Cfg.ExecuteRegionAddrBase[k], Cfg.ExecuteRegionLength[k], address);
      end
      return |pass;
    endfunction : is_inside_execute_regions

    function automatic logic is_inside_cacheable_regions (ariane_cfg_t Cfg, logic[63:0] address);
      automatic logic[NrMaxRules-1:0] pass;
      pass = '0;
      for (int unsigned k = 0; k < Cfg.NrCachedRegionRules; k++) begin
        pass[k] = range_check(Cfg.CachedRegionAddrBase[k], Cfg.CachedRegionLength[k], address);
      end
      return |pass;
    endfunction : is_inside_cacheable_regions

    // TODO: Slowly move those parameters to the new system.
    localparam NR_SB_ENTRIES = 8; // number of scoreboard entries
    localparam TRANS_ID_BITS = $clog2(NR_SB_ENTRIES); // depending on the number of scoreboard entries we need that many bits
                                                      // to uniquely identify the entry in the scoreboard
    localparam ASID_WIDTH    = (riscv::XLEN == 64) ? 16 : 1;
    localparam BITS_SATURATION_COUNTER = 2;
    localparam NR_COMMIT_PORTS = 2;

    localparam ENABLE_RENAME = 1'b0;

    localparam ISSUE_WIDTH = 1;
    // amount of pipeline registers inserted for load/store return path
    // this can be tuned to trade-off IPC vs. cycle time
    localparam int unsigned NR_LOAD_PIPE_REGS = 1;
    localparam int unsigned NR_STORE_PIPE_REGS = 0;

    // depth of store-buffers, this needs to be a power of two
    localparam int unsigned DEPTH_SPEC   = 4;

`ifdef WT_DCACHE
    // in this case we can use a small commit queue since we have a write buffer in the dcache
    // we could in principle do without the commit queue in this case, but the timing degrades if we do that due
    // to longer paths into the commit stage
    localparam int unsigned DEPTH_COMMIT = 4;
`else
    // allocate more space for the commit buffer to be on the save side, this needs to be a power of two
    localparam int unsigned DEPTH_COMMIT = 8;
`endif

`ifdef PITON_ARIANE
    // Floating-point extensions configuration
    localparam bit RVF = riscv::IS_XLEN64; // Is F extension enabled
    localparam bit RVD = riscv::IS_XLEN64; // Is D extension enabled
`else
    // Floating-point extensions configuration
    localparam bit RVF = riscv::IS_XLEN64; // Is F extension enabled
    localparam bit RVD = riscv::IS_XLEN64; // Is D extension enabled
`endif
    localparam bit RVA = 1'b1; // Is A extension enabled

    // Transprecision floating-point extensions configuration
    localparam bit XF16    = 1'b0; // Is half-precision float extension (Xf16) enabled
    localparam bit XF16ALT = 1'b0; // Is alternative half-precision float extension (Xf16alt) enabled
    localparam bit XF8     = 1'b0; // Is quarter-precision float extension (Xf8) enabled
    localparam bit XFVEC   = 1'b0; // Is vectorial float extension (Xfvec) enabled

    // Transprecision float unit
    localparam int unsigned LAT_COMP_FP32    = 'd2;
    localparam int unsigned LAT_COMP_FP64    = 'd3;
    localparam int unsigned LAT_COMP_FP16    = 'd1;
    localparam int unsigned LAT_COMP_FP16ALT = 'd1;
    localparam int unsigned LAT_COMP_FP8     = 'd1;
    localparam int unsigned LAT_DIVSQRT      = 'd2;
    localparam int unsigned LAT_NONCOMP      = 'd1;
    localparam int unsigned LAT_CONV         = 'd2;

    // --------------------------------------
    // vvvv Don't change these by hand! vvvv
    localparam bit FP_PRESENT = RVF | RVD | XF16 | XF16ALT | XF8;

    // Length of widest floating-point format
    localparam FLEN    = RVD     ? 64 : // D ext.
                         RVF     ? 32 : // F ext.
                         XF16    ? 16 : // Xf16 ext.
                         XF16ALT ? 16 : // Xf16alt ext.
                         XF8     ? 8 :  // Xf8 ext.
                         1;             // Unused in case of no FP

    localparam bit NSX = XF16 | XF16ALT | XF8 | XFVEC; // Are non-standard extensions present?

    localparam bit RVFVEC     = RVF     & XFVEC & FLEN>32; // FP32 vectors available if vectors and larger fmt enabled
    localparam bit XF16VEC    = XF16    & XFVEC & FLEN>16; // FP16 vectors available if vectors and larger fmt enabled
    localparam bit XF16ALTVEC = XF16ALT & XFVEC & FLEN>16; // FP16ALT vectors available if vectors and larger fmt enabled
    localparam bit XF8VEC     = XF8     & XFVEC & FLEN>8;  // FP8 vectors available if vectors and larger fmt enabled
    // ^^^^ until here ^^^^
    // ---------------------

    localparam riscv::xlen_t ARIANE_MARCHID = {{riscv::XLEN-32{1'b0}}, 32'd3};

    localparam riscv::xlen_t ISA_CODE = (RVA <<  0)  // A - Atomic Instructions extension
                                     | (1   <<  2)  // C - Compressed extension
                                     | (RVD <<  3)  // D - Double precsision floating-point extension
                                     | (RVF <<  5)  // F - Single precsision floating-point extension
                                     | (1   <<  8)  // I - RV32I/64I/128I base ISA
                                     | (1   << 12)  // M - Integer Multiply/Divide extension
                                     | (0   << 13)  // N - User level interrupts supported
                                     | (1   << 18)  // S - Supervisor mode implemented
                                     | (1   << 20)  // U - User mode implemented
                                     | (NSX << 23)  // X - Non-standard extensions present
                                     | ((riscv::XLEN == 64 ? 2 : 1) << riscv::XLEN-2);  // MXL

    // 32 registers + 1 bit for re-naming = 6
    localparam REG_ADDR_SIZE = 6;
    localparam NR_WB_PORTS = 4;

    // static debug hartinfo
    localparam dm::hartinfo_t DebugHartInfo = '{
                                                zero1:        '0,
                                                nscratch:      2, // Debug module needs at least two scratch regs
                                                zero0:        '0,
                                                dataaccess: 1'b1, // data registers are memory mapped in the debugger
                                                datasize: dm::DataCount,
                                                dataaddr: dm::DataAddr
                                              };

    // enables a commit log which matches spikes commit log format for easier trace comparison
    localparam bit ENABLE_SPIKE_COMMIT_LOG = 1'b1;

    // ------------- Dangerouse -------------
    // if set to zero a flush will not invalidate the cache-lines, in a single core environment
    // where coherence is not necessary this can improve performance. This needs to be switched on
    // when more than one core is in a system
    localparam logic INVALIDATE_ON_FLUSH = 1'b1;
`ifdef SPIKE_TANDEM
    // enable performance cycle counter, if set to zero mcycle will be incremented
    // with instret (non RISC-V conformal)
    localparam bit ENABLE_CYCLE_COUNT = 1'b0;
    // mark WIF as nop
    localparam bit ENABLE_WFI = 1'b0;
    // Spike zeros tval on all exception except memory faults
    localparam bit ZERO_TVAL = 1'b1;
`else
    localparam bit ENABLE_CYCLE_COUNT = 1'b1;
    localparam bit ENABLE_WFI = 1'b1;
    localparam bit ZERO_TVAL = 1'b0;
`endif
    // read mask for SSTATUS over MMSTATUS
    localparam logic [63:0] SMODE_STATUS_READ_MASK = riscv::SSTATUS_UIE
                                                   | riscv::SSTATUS_SIE
                                                   | riscv::SSTATUS_SPIE
                                                   | riscv::SSTATUS_SPP
                                                   | riscv::SSTATUS_FS
                                                   | riscv::SSTATUS_XS
                                                   | riscv::SSTATUS_SUM
                                                   | riscv::SSTATUS_MXR
                                                   | riscv::SSTATUS_UPIE
                                                   | riscv::SSTATUS_SPIE
                                                   | riscv::SSTATUS_UXL
                                                   | riscv::SSTATUS_SD;

    localparam logic [63:0] SMODE_STATUS_WRITE_MASK = riscv::SSTATUS_SIE
                                                    | riscv::SSTATUS_SPIE
                                                    | riscv::SSTATUS_SPP
                                                    | riscv::SSTATUS_FS
                                                    | riscv::SSTATUS_SUM
                                                    | riscv::SSTATUS_MXR;
    // ---------------
    // Fetch Stage
    // ---------------

    // leave as is (fails with >8 entries and wider fetch width)
    localparam int unsigned FETCH_FIFO_DEPTH  = 4;
    localparam int unsigned FETCH_WIDTH       = 32;
    // maximum instructions we can fetch on one request (we support compressed instructions)
    localparam int unsigned INSTR_PER_FETCH = FETCH_WIDTH / 16;

    // Only use struct when signals have same direction
    // exception
    typedef struct packed {
         riscv::xlen_t       cause; // cause of exception
         riscv::xlen_t       tval;  // additional information of causing exception (e.g.: instruction causing it),
                             // address of LD/ST fault
         logic        valid;
    } exception_t;

    typedef enum logic [2:0] {
      NoCF,   // No control flow prediction
      Branch, // Branch
      Jump,   // Jump to address from immediate
      JumpR,  // Jump to address from registers
      Return  // Return Address Prediction
    } cf_t;

    // branch-predict
    // this is the struct we get back from ex stage and we will use it to update
    // all the necessary data structures
    // bp_resolve_t
    typedef struct packed {
        logic                   valid;           // prediction with all its values is valid
        logic [riscv::VLEN-1:0] pc;              // PC of predict or mis-predict
        logic [riscv::VLEN-1:0] target_address;  // target address at which to jump, or not
        logic                   is_mispredict;   // set if this was a mis-predict
        logic                   is_taken;        // branch is taken
        cf_t                    cf_type;         // Type of control flow change
    } bp_resolve_t;

    // branchpredict scoreboard entry
    // this is the struct which we will inject into the pipeline to guide the various
    // units towards the correct branch decision and resolve
    typedef struct packed {
        cf_t                    cf;              // type of control flow prediction
        logic [riscv::VLEN-1:0] predict_address; // target address at which to jump, or not
    } branchpredict_sbe_t;

    typedef struct packed {
        logic                   valid;
        logic [riscv::VLEN-1:0] pc;             // update at PC
        logic [riscv::VLEN-1:0] target_address;
    } btb_update_t;

    typedef struct packed {
        logic                   valid;
        logic [riscv::VLEN-1:0] target_address;
    } btb_prediction_t;

    typedef struct packed {
        logic                   valid;
        logic [riscv::VLEN-1:0] ra;
    } ras_t;

    typedef struct packed {
        logic                   valid;
        logic [riscv::VLEN-1:0] pc;          // update at PC
        logic                   taken;
    } bht_update_t;

    typedef struct packed {
        logic       valid;
        logic       taken;
    } bht_prediction_t;

    typedef enum logic[3:0] {
        NONE,      // 0
        LOAD,      // 1
        STORE,     // 2
        ALU,       // 3
        CTRL_FLOW, // 4
        MULT,      // 5
        CSR,       // 6
        FPU,       // 7
        FPU_VEC    // 8
    } fu_t;

    localparam EXC_OFF_RST      = 8'h80;

    localparam SupervisorIrq = 1;
    localparam MachineIrq = 0;

    // All information needed to determine whether we need to associate an interrupt
    // with the corresponding instruction or not.
    typedef struct packed {
      riscv::xlen_t       mie;
      riscv::xlen_t       mip;
      riscv::xlen_t       mideleg;
      logic        sie;
      logic        global_enable;
    } irq_ctrl_t;

    // ---------------
    // Cache config
    // ---------------

// for usage in OpenPiton we have to propagate the openpiton L15 configuration from l15.h
`ifdef PITON_ARIANE

`ifndef CONFIG_L1I_CACHELINE_WIDTH
    `define CONFIG_L1I_CACHELINE_WIDTH 128
`endif

`ifndef CONFIG_L1I_ASSOCIATIVITY
    `define CONFIG_L1I_ASSOCIATIVITY 4
`endif

`ifndef CONFIG_L1I_SIZE
    `define CONFIG_L1I_SIZE 16*1024
`endif

`ifndef CONFIG_L1D_CACHELINE_WIDTH
    `define CONFIG_L1D_CACHELINE_WIDTH 128
`endif

`ifndef CONFIG_L1D_ASSOCIATIVITY
    `define CONFIG_L1D_ASSOCIATIVITY 8
`endif

`ifndef CONFIG_L1D_SIZE
    `define CONFIG_L1D_SIZE 32*1024
`endif

    // I$
    localparam int unsigned ICACHE_LINE_WIDTH  = `CONFIG_L1I_CACHELINE_WIDTH;
    localparam int unsigned ICACHE_SET_ASSOC   = `CONFIG_L1I_ASSOCIATIVITY;
    localparam int unsigned ICACHE_INDEX_WIDTH = $clog2(`CONFIG_L1I_SIZE / ICACHE_SET_ASSOC);
    localparam int unsigned ICACHE_TAG_WIDTH   = riscv::PLEN - ICACHE_INDEX_WIDTH;
    // D$
    localparam int unsigned DCACHE_LINE_WIDTH  = `CONFIG_L1D_CACHELINE_WIDTH;
    localparam int unsigned DCACHE_SET_ASSOC   = `CONFIG_L1D_ASSOCIATIVITY;
    localparam int unsigned DCACHE_INDEX_WIDTH = $clog2(`CONFIG_L1D_SIZE / DCACHE_SET_ASSOC);
    localparam int unsigned DCACHE_TAG_WIDTH   = riscv::PLEN - DCACHE_INDEX_WIDTH;
`else
    // I$
		localparam int unsigned CONFIG_L1I_SIZE    = 16*1024;
    localparam int unsigned ICACHE_SET_ASSOC   = 4;
    localparam int unsigned ICACHE_INDEX_WIDTH = $clog2(CONFIG_L1I_SIZE / ICACHE_SET_ASSOC);  // in bit, contains also offset width
    localparam int unsigned ICACHE_TAG_WIDTH   = riscv::PLEN-ICACHE_INDEX_WIDTH;  // in bit
    localparam int unsigned ICACHE_LINE_WIDTH  = 128; // in bit
    // D$
		localparam int unsigned CONFIG_L1D_SIZE    = 32*1024;
	  localparam int unsigned DCACHE_SET_ASSOC   = 8;
    localparam int unsigned DCACHE_INDEX_WIDTH = $clog2(CONFIG_L1D_SIZE / DCACHE_SET_ASSOC);  // in bit, contains also offset width
    localparam int unsigned DCACHE_TAG_WIDTH   = riscv::PLEN-DCACHE_INDEX_WIDTH;  // in bit
    localparam int unsigned DCACHE_LINE_WIDTH  = 128; // in bit
`endif

    // ---------------
    // EX Stage
    // ---------------
    typedef enum logic [6:0] { // basic ALU op
                               ADD, SUB, ADDW, SUBW,
                               // logic operations
                               XORL, ORL, ANDL,
                               // shifts
                               SRA, SRL, SLL, SRLW, SLLW, SRAW,
                               // comparisons
                               LTS, LTU, GES, GEU, EQ, NE,
                               // jumps
                               JALR, BRANCH,
                               // set lower than operations
                               SLTS, SLTU,
                               // CSR functions
                               MRET, SRET, DRET, ECALL, WFI, FENCE, FENCE_I, SFENCE_VMA, CSR_WRITE, CSR_READ, CSR_SET, CSR_CLEAR,
                               // LSU functions
                               LD, SD, LW, LWU, SW, LH, LHU, SH, LB, SB, LBU,
                               // Atomic Memory Operations
                               AMO_LRW, AMO_LRD, AMO_SCW, AMO_SCD,
                               AMO_SWAPW, AMO_ADDW, AMO_ANDW, AMO_ORW, AMO_XORW, AMO_MAXW, AMO_MAXWU, AMO_MINW, AMO_MINWU,
                               AMO_SWAPD, AMO_ADDD, AMO_ANDD, AMO_ORD, AMO_XORD, AMO_MAXD, AMO_MAXDU, AMO_MIND, AMO_MINDU,
                               // Multiplications
                               MUL, MULH, MULHU, MULHSU, MULW,
                               // Divisions
                               DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW,
                               // Floating-Point Load and Store Instructions
                               FLD, FLW, FLH, FLB, FSD, FSW, FSH, FSB,
                               // Floating-Point Computational Instructions
                               FADD, FSUB, FMUL, FDIV, FMIN_MAX, FSQRT, FMADD, FMSUB, FNMSUB, FNMADD,
                               // Floating-Point Conversion and Move Instructions
                               FCVT_F2I, FCVT_I2F, FCVT_F2F, FSGNJ, FMV_F2X, FMV_X2F,
                               // Floating-Point Compare Instructions
                               FCMP,
                               // Floating-Point Classify Instruction
                               FCLASS,
                               // Vectorial Floating-Point Instructions that don't directly map onto the scalar ones
                               VFMIN, VFMAX, VFSGNJ, VFSGNJN, VFSGNJX, VFEQ, VFNE, VFLT, VFGE, VFLE, VFGT, VFCPKAB_S, VFCPKCD_S, VFCPKAB_D, VFCPKCD_D
                             } fu_op;

    typedef struct packed {
        fu_t                      fu;
        fu_op                     operator;
        riscv::xlen_t             operand_a;
        riscv::xlen_t             operand_b;
        riscv::xlen_t             imm;
        logic [TRANS_ID_BITS-1:0] trans_id;
    } fu_data_t;

    function automatic logic op_is_branch (input fu_op op);
        unique case (op) inside
            EQ, NE, LTS, GES, LTU, GEU: return 1'b1;
            default                   : return 1'b0; // all other ops
        endcase
    endfunction

    // -------------------------------
    // Extract Src/Dst FP Reg from Op
    // -------------------------------
    function automatic logic is_rs1_fpr (input fu_op op);
        if (FP_PRESENT) begin // makes function static for non-fp case
            unique case (op) inside
                [FMUL:FNMADD],                   // Computational Operations (except ADD/SUB)
                FCVT_F2I,                        // Float-Int Casts
                FCVT_F2F,                        // Float-Float Casts
                FSGNJ,                           // Sign Injections
                FMV_F2X,                         // FPR-GPR Moves
                FCMP,                            // Comparisons
                FCLASS,                          // Classifications
                [VFMIN:VFCPKCD_D] : return 1'b1; // Additional Vectorial FP ops
                default           : return 1'b0; // all other ops
            endcase
        end else
            return 1'b0;
    endfunction

    function automatic logic is_rs2_fpr (input fu_op op);
        if (FP_PRESENT) begin // makes function static for non-fp case
            unique case (op) inside
                [FSD:FSB],                       // FP Stores
                [FADD:FMIN_MAX],                 // Computational Operations (no sqrt)
                [FMADD:FNMADD],                  // Fused Computational Operations
                FCVT_F2F,                        // Vectorial F2F Conversions requrie target
                [FSGNJ:FMV_F2X],                 // Sign Injections and moves mapped to SGNJ
                FCMP,                            // Comparisons
                [VFMIN:VFCPKCD_D] : return 1'b1; // Additional Vectorial FP ops
                default           : return 1'b0; // all other ops
            endcase
        end else
            return 1'b0;
    endfunction

    // ternary operations encode the rs3 address in the imm field, also add/sub
    function automatic logic is_imm_fpr (input fu_op op);
        if (FP_PRESENT) begin // makes function static for non-fp case
            unique case (op) inside
                [FADD:FSUB],                         // ADD/SUB need inputs as Operand B/C
                [FMADD:FNMADD],                      // Fused Computational Operations
                [VFCPKAB_S:VFCPKCD_D] : return 1'b1; // Vectorial FP cast and pack ops
                default               : return 1'b0; // all other ops
            endcase
        end else
            return 1'b0;
    endfunction

    function automatic logic is_rd_fpr (input fu_op op);
        if (FP_PRESENT) begin // makes function static for non-fp case
            unique case (op) inside
                [FLD:FLB],                           // FP Loads
                [FADD:FNMADD],                       // Computational Operations
                FCVT_I2F,                            // Int-Float Casts
                FCVT_F2F,                            // Float-Float Casts
                FSGNJ,                               // Sign Injections
                FMV_X2F,                             // GPR-FPR Moves
                [VFMIN:VFSGNJX],                     // Vectorial MIN/MAX and SGNJ
                [VFCPKAB_S:VFCPKCD_D] : return 1'b1; // Vectorial FP cast and pack ops
                default               : return 1'b0; // all other ops
            endcase
        end else
            return 1'b0;
    endfunction

    function automatic logic is_amo (fu_op op);
        case (op) inside
            [AMO_LRW:AMO_MINDU]: begin
                return 1'b1;
            end
            default: return 1'b0;
        endcase
    endfunction

    typedef struct packed {
        logic                     valid;
        logic [riscv::VLEN-1:0]   vaddr;
        logic                     overflow;
        logic [63:0]              data;
        logic [7:0]               be;
        fu_t                      fu;
        fu_op                     operator;
        logic [TRANS_ID_BITS-1:0] trans_id;
    } lsu_ctrl_t;

    // ---------------
    // IF/ID Stage
    // ---------------
    // store the decompressed instruction
    typedef struct packed {
        logic [riscv::VLEN-1:0] address;        // the address of the instructions from below
        logic [31:0]            instruction;    // instruction word
        branchpredict_sbe_t     branch_predict; // this field contains branch prediction information regarding the forward branch path
        exception_t             ex;             // this field contains exceptions which might have happened earlier, e.g.: fetch exceptions
    } fetch_entry_t;

    // ---------------
    // ID/EX/WB Stage
    // ---------------
    typedef struct packed {
        logic [riscv::VLEN-1:0]   pc;            // PC of instruction
        logic [TRANS_ID_BITS-1:0] trans_id;      // this can potentially be simplified, we could index the scoreboard entry
                                                 // with the transaction id in any case make the width more generic
        fu_t                      fu;            // functional unit to use
        fu_op                     op;            // operation to perform in each functional unit
        logic [REG_ADDR_SIZE-1:0] rs1;           // register source address 1
        logic [REG_ADDR_SIZE-1:0] rs2;           // register source address 2
        logic [REG_ADDR_SIZE-1:0] rd;            // register destination address
        riscv::xlen_t             result;        // for unfinished instructions this field also holds the immediate,
                                                 // for unfinished floating-point that are partly encoded in rs2, this field also holds rs2
                                                 // for unfinished floating-point fused operations (FMADD, FMSUB, FNMADD, FNMSUB)
                                                 // this field holds the address of the third operand from the floating-point register file
        logic                     valid;         // is the result valid
        logic                     use_imm;       // should we use the immediate as operand b?
        logic                     use_zimm;      // use zimm as operand a
        logic                     use_pc;        // set if we need to use the PC as operand a, PC from exception
        exception_t               ex;            // exception has occurred
        branchpredict_sbe_t       bp;            // branch predict scoreboard data structure
        logic                     is_compressed; // signals a compressed instructions, we need this information at the commit stage if
                                                 // we want jump accordingly e.g.: +4, +2
    } scoreboard_entry_t;

    // --------------------
    // Atomics
    // --------------------
    typedef enum logic [3:0] {
        AMO_NONE =4'b0000,
        AMO_LR   =4'b0001,
        AMO_SC   =4'b0010,
        AMO_SWAP =4'b0011,
        AMO_ADD  =4'b0100,
        AMO_AND  =4'b0101,
        AMO_OR   =4'b0110,
        AMO_XOR  =4'b0111,
        AMO_MAX  =4'b1000,
        AMO_MAXU =4'b1001,
        AMO_MIN  =4'b1010,
        AMO_MINU =4'b1011,
        AMO_CAS1 =4'b1100, // unused, not part of riscv spec, but provided in OpenPiton
        AMO_CAS2 =4'b1101  // unused, not part of riscv spec, but provided in OpenPiton
    } amo_t;

    typedef struct packed {
        logic                  valid;      // valid flag
        logic                  is_2M;      //
        logic                  is_1G;      //
        logic [26:0]           vpn;
        logic [ASID_WIDTH-1:0] asid;
        riscv::pte_t           content;
    } tlb_update_t;

    // Bits required for representation of physical address space as 4K pages
    // (e.g. 27*4K == 39bit address space).
    localparam PPN4K_WIDTH = 38;

    typedef enum logic [1:0] {
      FE_NONE,
      FE_INSTR_ACCESS_FAULT,
      FE_INSTR_PAGE_FAULT
    } frontend_exception_t;

    // ----------------------
    // cache request ports
    // ----------------------
    // I$ address translation requests
    typedef struct packed {
        logic                     fetch_valid;     // address translation valid
        logic [riscv::PLEN-1:0]   fetch_paddr;     // physical address in
        exception_t               fetch_exception; // exception occurred during fetch
    } icache_areq_i_t;

    typedef struct packed {
        logic                     fetch_req;       // address translation request
        logic [riscv::VLEN-1:0]   fetch_vaddr;     // virtual address out
    } icache_areq_o_t;

    // I$ data requests
    typedef struct packed {
        logic                     req;                    // we request a new word
        logic                     kill_s1;                // kill the current request
        logic                     kill_s2;                // kill the last request
        logic                     spec;                   // request is speculative
        logic [riscv::VLEN-1:0]   vaddr;                  // 1st cycle: 12 bit index is taken for lookup
    } icache_dreq_i_t;

    typedef struct packed {
        logic                     ready;                  // icache is ready
        logic                     valid;                  // signals a valid read
        logic [FETCH_WIDTH-1:0]   data;                   // 2+ cycle out: tag
        logic [riscv::VLEN-1:0]   vaddr;                  // virtual address out
        exception_t               ex;                     // we've encountered an exception
    } icache_dreq_o_t;

    // AMO request going to cache. this request is unconditionally valid as soon
    // as request goes high.
    // Furthermore, those signals are kept stable until the response indicates
    // completion by asserting ack.
    typedef struct packed {
        logic        req;       // this request is valid
        amo_t        amo_op;    // atomic memory operation to perform
        logic [1:0]  size;      // 2'b10 --> word operation, 2'b11 --> double word operation
        logic [63:0] operand_a; // address
        logic [63:0] operand_b; // data as layouted in the register
    } amo_req_t;

    // AMO response coming from cache.
    typedef struct packed {
        logic        ack;    // response is valid
        logic [63:0] result; // sign-extended, result
    } amo_resp_t;

    // D$ data requests
    typedef struct packed {
        logic [DCACHE_INDEX_WIDTH-1:0] address_index;
        logic [DCACHE_TAG_WIDTH-1:0]   address_tag;
        logic [63:0]                   data_wdata;
        logic                          data_req;
        logic                          data_we;
        logic [7:0]                    data_be;
        logic [1:0]                    data_size;
        logic                          kill_req;
        logic                          tag_valid;
    } dcache_req_i_t;

    typedef struct packed {
        logic                          data_gnt;
        logic                          data_rvalid;
        logic [63:0]                   data_rdata;
    } dcache_req_o_t;

    // ----------------------
    // Arithmetic Functions
    // ----------------------
    function automatic riscv::xlen_t sext32 (logic [31:0] operand);
        return {{riscv::XLEN-32{operand[31]}}, operand[31:0]};
    endfunction

    // ----------------------
    // Immediate functions
    // ----------------------
    function automatic logic [riscv::VLEN-1:0] uj_imm (logic [31:0] instruction_i);
        return { {44+riscv::VLEN-64 {instruction_i[31]}}, instruction_i[19:12], instruction_i[20], instruction_i[30:21], 1'b0 };
    endfunction

    function automatic logic [riscv::VLEN-1:0] i_imm (logic [31:0] instruction_i);
        return { {52+riscv::VLEN-64 {instruction_i[31]}}, instruction_i[31:20] };
    endfunction

    function automatic logic [riscv::VLEN-1:0] sb_imm (logic [31:0] instruction_i);
        return { {51+riscv::VLEN-64 {instruction_i[31]}}, instruction_i[31], instruction_i[7], instruction_i[30:25], instruction_i[11:8], 1'b0 };
    endfunction

    // ----------------------
    // LSU Functions
    // ----------------------
    // align data to address e.g.: shift data to be naturally 64
    function automatic riscv::xlen_t data_align (logic [2:0] addr, logic [63:0] data);
        // Set addr[2] to 1'b0 when 32bits
        logic [2:0] addr_tmp = {(addr[2] && riscv::IS_XLEN64), addr[1:0]};
        logic [63:0] data_tmp = {64{1'b0}};
        case (addr_tmp)
            3'b000: data_tmp[riscv::XLEN-1:0] = {data[riscv::XLEN-1:0]};
            3'b001: data_tmp[riscv::XLEN-1:0] = {data[riscv::XLEN-9:0],  data[riscv::XLEN-1:riscv::XLEN-8]};
            3'b010: data_tmp[riscv::XLEN-1:0] = {data[riscv::XLEN-17:0], data[riscv::XLEN-1:riscv::XLEN-16]};
            3'b011: data_tmp[riscv::XLEN-1:0] = {data[riscv::XLEN-25:0], data[riscv::XLEN-1:riscv::XLEN-24]};
            3'b100: data_tmp = {data[31:0], data[63:32]};
            3'b101: data_tmp = {data[23:0], data[63:24]};
            3'b110: data_tmp = {data[15:0], data[63:16]};
            3'b111: data_tmp = {data[7:0],  data[63:8]};
        endcase
        return data_tmp[riscv::XLEN-1:0];
    endfunction

    // generate byte enable mask
    function automatic logic [7:0] be_gen(logic [2:0] addr, logic [1:0] size);
        case (size)
            2'b11: begin
                return 8'b1111_1111;
            end
            2'b10: begin
                case (addr[2:0])
                    3'b000: return 8'b0000_1111;
                    3'b001: return 8'b0001_1110;
                    3'b010: return 8'b0011_1100;
                    3'b011: return 8'b0111_1000;
                    3'b100: return 8'b1111_0000;
                endcase
            end
            2'b01: begin
                case (addr[2:0])
                    3'b000: return 8'b0000_0011;
                    3'b001: return 8'b0000_0110;
                    3'b010: return 8'b0000_1100;
                    3'b011: return 8'b0001_1000;
                    3'b100: return 8'b0011_0000;
                    3'b101: return 8'b0110_0000;
                    3'b110: return 8'b1100_0000;
                endcase
            end
            2'b00: begin
                case (addr[2:0])
                    3'b000: return 8'b0000_0001;
                    3'b001: return 8'b0000_0010;
                    3'b010: return 8'b0000_0100;
                    3'b011: return 8'b0000_1000;
                    3'b100: return 8'b0001_0000;
                    3'b101: return 8'b0010_0000;
                    3'b110: return 8'b0100_0000;
                    3'b111: return 8'b1000_0000;
                endcase
            end
        endcase
        return 8'b0;
    endfunction

    // ----------------------
    // Extract Bytes from Op
    // ----------------------
    function automatic logic [1:0] extract_transfer_size(fu_op op);
        case (op)
            LD, SD, FLD, FSD,
            AMO_LRD,   AMO_SCD,
            AMO_SWAPD, AMO_ADDD,
            AMO_ANDD,  AMO_ORD,
            AMO_XORD,  AMO_MAXD,
            AMO_MAXDU, AMO_MIND,
            AMO_MINDU: begin
                return 2'b11;
            end
            LW, LWU, SW, FLW, FSW,
            AMO_LRW,   AMO_SCW,
            AMO_SWAPW, AMO_ADDW,
            AMO_ANDW,  AMO_ORW,
            AMO_XORW,  AMO_MAXW,
            AMO_MAXWU, AMO_MINW,
            AMO_MINWU: begin
                return 2'b10;
            end
            LH, LHU, SH, FLH, FSH: return 2'b01;
            LB, LBU, SB, FLB, FSB: return 2'b00;
            default:     return 2'b11;
        endcase
    endfunction
endpackage

package fpnew_pkg;

  // ---------
  // FP TYPES
  // ---------
  // | Enumerator | Format           | Width  | EXP_BITS | MAN_BITS
  // |:----------:|------------------|-------:|:--------:|:--------:
  // | FP32       | IEEE binary32    | 32 bit | 8        | 23
  // | FP64       | IEEE binary64    | 64 bit | 11       | 52
  // | FP16       | IEEE binary16    | 16 bit | 5        | 10
  // | FP8        | binary8          |  8 bit | 5        | 2
  // | FP16ALT    | binary16alt      | 16 bit | 8        | 7
  // *NOTE:* Add new formats only at the end of the enumeration for backwards compatibilty!

  // Encoding for a format
  typedef struct packed {
    int unsigned exp_bits;
    int unsigned man_bits;
  } fp_encoding_t;

  localparam int unsigned NUM_FP_FORMATS = 5; // change me to add formats
  localparam int unsigned FP_FORMAT_BITS = $clog2(NUM_FP_FORMATS);

  // FP formats
  typedef enum logic [FP_FORMAT_BITS-1:0] {
    FP32    = 'd0,
    FP64    = 'd1,
    FP16    = 'd2,
    FP8     = 'd3,
    FP16ALT = 'd4
    // add new formats here
  } fp_format_e;

  // Encodings for supported FP formats
  localparam fp_encoding_t [0:NUM_FP_FORMATS-1] FP_ENCODINGS  = '{
    '{8,  23}, // IEEE binary32 (single)
    '{11, 52}, // IEEE binary64 (double)
    '{5,  10}, // IEEE binary16 (half)
    '{5,  2},  // custom binary8
    '{8,  7}   // custom binary16alt
    // add new formats here
  };

  typedef logic [0:NUM_FP_FORMATS-1]       fmt_logic_t;    // Logic indexed by FP format (for masks)
  typedef logic [0:NUM_FP_FORMATS-1][31:0] fmt_unsigned_t; // Unsigned indexed by FP format

  localparam fmt_logic_t CPK_FORMATS = 5'b11000; // FP32 and FP64 can provide CPK only

  // ---------
  // INT TYPES
  // ---------
  // | Enumerator | Width  |
  // |:----------:|-------:|
  // | INT8       |  8 bit |
  // | INT16      | 16 bit |
  // | INT32      | 32 bit |
  // | INT64      | 64 bit |
  // *NOTE:* Add new formats only at the end of the enumeration for backwards compatibilty!

  localparam int unsigned NUM_INT_FORMATS = 4; // change me to add formats
  localparam int unsigned INT_FORMAT_BITS = $clog2(NUM_INT_FORMATS);

  // Int formats
  typedef enum logic [INT_FORMAT_BITS-1:0] {
    INT8,
    INT16,
    INT32,
    INT64
    // add new formats here
  } int_format_e;

  // Returns the width of an INT format by index
  function automatic int unsigned int_width(int_format_e ifmt);
    unique case (ifmt)
      INT8:  return 8;
      INT16: return 16;
      INT32: return 32;
      INT64: return 64;
    endcase
  endfunction

  typedef logic [0:NUM_INT_FORMATS-1] ifmt_logic_t; // Logic indexed by INT format (for masks)

  // --------------
  // FP OPERATIONS
  // --------------
  localparam int unsigned NUM_OPGROUPS = 4;

  // Each FP operation belongs to an operation group
  typedef enum logic [1:0] {
    ADDMUL, DIVSQRT, NONCOMP, CONV
  } opgroup_e;

  localparam int unsigned OP_BITS = 4;

  typedef enum logic [OP_BITS-1:0] {
    FMADD, FNMSUB, ADD, MUL,     // ADDMUL operation group
    DIV, SQRT,                   // DIVSQRT operation group
    SGNJ, MINMAX, CMP, CLASSIFY, // NONCOMP operation group
    F2F, F2I, I2F, CPKAB, CPKCD  // CONV operation group
  } operation_e;

  // -------------------
  // RISC-V FP-SPECIFIC
  // -------------------
  // Rounding modes
  typedef enum logic [2:0] {
    RNE = 3'b000,
    RTZ = 3'b001,
    RDN = 3'b010,
    RUP = 3'b011,
    RMM = 3'b100,
    DYN = 3'b111
  } roundmode_e;

  // Status flags
  typedef struct packed {
    logic NV; // Invalid
    logic DZ; // Divide by zero
    logic OF; // Overflow
    logic UF; // Underflow
    logic NX; // Inexact
  } status_t;

  // Information about a floating point value
  typedef struct packed {
    logic is_normal;     // is the value normal
    logic is_subnormal;  // is the value subnormal
    logic is_zero;       // is the value zero
    logic is_inf;        // is the value infinity
    logic is_nan;        // is the value NaN
    logic is_signalling; // is the value a signalling NaN
    logic is_quiet;      // is the value a quiet NaN
    logic is_boxed;      // is the value properly NaN-boxed (RISC-V specific)
  } fp_info_t;

  // Classification mask
  typedef enum logic [9:0] {
    NEGINF     = 10'b00_0000_0001,
    NEGNORM    = 10'b00_0000_0010,
    NEGSUBNORM = 10'b00_0000_0100,
    NEGZERO    = 10'b00_0000_1000,
    POSZERO    = 10'b00_0001_0000,
    POSSUBNORM = 10'b00_0010_0000,
    POSNORM    = 10'b00_0100_0000,
    POSINF     = 10'b00_1000_0000,
    SNAN       = 10'b01_0000_0000,
    QNAN       = 10'b10_0000_0000
  } classmask_e;

  // ------------------
  // FPU configuration
  // ------------------
  // Pipelining registers can be inserted (at elaboration time) into operational units
  typedef enum logic [1:0] {
    BEFORE,     // registers are inserted at the inputs of the unit
    AFTER,      // registers are inserted at the outputs of the unit
    INSIDE,     // registers are inserted at predetermined (suboptimal) locations in the unit
    DISTRIBUTED // registers are evenly distributed, INSIDE >= AFTER >= BEFORE
  } pipe_config_t;

  // Arithmetic units can be arranged in parallel (per format), merged (multi-format) or not at all.
  typedef enum logic [1:0] {
    DISABLED, // arithmetic units are not generated
    PARALLEL, // arithmetic units are generated in prallel slices, one for each format
    MERGED    // arithmetic units are contained within a merged unit holding multiple formats
  } unit_type_t;

  // Array of unit types indexed by format
  typedef unit_type_t [0:NUM_FP_FORMATS-1] fmt_unit_types_t;

  // Array of format-specific unit types by opgroup
  typedef fmt_unit_types_t [0:NUM_OPGROUPS-1] opgrp_fmt_unit_types_t;
  // same with unsigned
  typedef fmt_unsigned_t [0:NUM_OPGROUPS-1] opgrp_fmt_unsigned_t;

  // FPU configuration: features
  typedef struct packed {
    int unsigned Width;
    logic        EnableVectors;
    logic        EnableNanBox;
    fmt_logic_t  FpFmtMask;
    ifmt_logic_t IntFmtMask;
  } fpu_features_t;

  localparam fpu_features_t RV64D = '{
    Width:         64,
    EnableVectors: 1'b0,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b11000,
    IntFmtMask:    4'b0011
  };

  localparam fpu_features_t RV32D = '{
    Width:         64,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b11000,
    IntFmtMask:    4'b0010
  };

  localparam fpu_features_t RV32F = '{
    Width:         32,
    EnableVectors: 1'b0,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b10000,
    IntFmtMask:    4'b0010
  };

  localparam fpu_features_t RV64D_Xsflt = '{
    Width:         64,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b11111,
    IntFmtMask:    4'b1111
  };

  localparam fpu_features_t RV32F_Xsflt = '{
    Width:         32,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b10111,
    IntFmtMask:    4'b1110
  };

  localparam fpu_features_t RV32F_Xf16alt_Xfvec = '{
    Width:         32,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b10001,
    IntFmtMask:    4'b0110
  };


  // FPU configuraion: implementation
  typedef struct packed {
    opgrp_fmt_unsigned_t   PipeRegs;
    opgrp_fmt_unit_types_t UnitTypes;
    pipe_config_t          PipeConfig;
  } fpu_implementation_t;

  localparam fpu_implementation_t DEFAULT_NOREGS = '{
    PipeRegs:   '{default: 0},
    UnitTypes:  '{'{default: PARALLEL}, // ADDMUL
                  '{default: MERGED},   // DIVSQRT
                  '{default: PARALLEL}, // NONCOMP
                  '{default: MERGED}},  // CONV
    PipeConfig: BEFORE
  };

  localparam fpu_implementation_t DEFAULT_SNITCH = '{
    PipeRegs:   '{default: 1},
    UnitTypes:  '{'{default: PARALLEL}, // ADDMUL
                  '{default: DISABLED}, // DIVSQRT
                  '{default: PARALLEL}, // NONCOMP
                  '{default: MERGED}},  // CONV
    PipeConfig: BEFORE
  };

  // -----------------------
  // Synthesis optimization
  // -----------------------
  localparam logic DONT_CARE = 1'b1; // the value to assign as don't care

  // -------------------------
  // General helper functions
  // -------------------------
  function automatic int minimum(int a, int b);
    return (a < b) ? a : b;
  endfunction

  function automatic int maximum(int a, int b);
    return (a > b) ? a : b;
  endfunction

  // -------------------------------------------
  // Helper functions for FP formats and values
  // -------------------------------------------
  // Returns the width of a FP format
  function automatic int unsigned fp_width(fp_format_e fmt);
    return FP_ENCODINGS[fmt].exp_bits + FP_ENCODINGS[fmt].man_bits + 1;
  endfunction

  // Returns the widest FP format present
  function automatic int unsigned max_fp_width(fmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i])
        res = unsigned'(maximum(res, fp_width(fp_format_e'(i))));
    return res;
  endfunction

  // Returns the narrowest FP format present
  function automatic int unsigned min_fp_width(fmt_logic_t cfg);
    automatic int unsigned res = max_fp_width(cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i])
        res = unsigned'(minimum(res, fp_width(fp_format_e'(i))));
    return res;
  endfunction

  // Returns the number of expoent bits for a format
  function automatic int unsigned exp_bits(fp_format_e fmt);
    return FP_ENCODINGS[fmt].exp_bits;
  endfunction

  // Returns the number of mantissa bits for a format
  function automatic int unsigned man_bits(fp_format_e fmt);
    return FP_ENCODINGS[fmt].man_bits;
  endfunction

  // Returns the bias value for a given format (as per IEEE 754-2008)
  function automatic int unsigned bias(fp_format_e fmt);
    return unsigned'(2**(FP_ENCODINGS[fmt].exp_bits-1)-1); // symmetrical bias
  endfunction

  function automatic fp_encoding_t super_format(fmt_logic_t cfg);
    automatic fp_encoding_t res;
    res = '0;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      if (cfg[fmt]) begin // only active format
        res.exp_bits = unsigned'(maximum(res.exp_bits, exp_bits(fp_format_e'(fmt))));
        res.man_bits = unsigned'(maximum(res.man_bits, man_bits(fp_format_e'(fmt))));
      end
    return res;
  endfunction

  // -------------------------------------------
  // Helper functions for INT formats and values
  // -------------------------------------------
  // Returns the widest INT format present
  function automatic int unsigned max_int_width(ifmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++) begin
      if (cfg[ifmt]) res = maximum(res, int_width(int_format_e'(ifmt)));
    end
    return res;
  endfunction

  // --------------------------------------------------
  // Helper functions for operations and FPU structure
  // --------------------------------------------------
  // Returns the operation group of the given operation
  function automatic opgroup_e get_opgroup(operation_e op);
    unique case (op)
      FMADD, FNMSUB, ADD, MUL:     return ADDMUL;
      DIV, SQRT:                   return DIVSQRT;
      SGNJ, MINMAX, CMP, CLASSIFY: return NONCOMP;
      F2F, F2I, I2F, CPKAB, CPKCD: return CONV;
      default:                     return NONCOMP;
    endcase
  endfunction

  // Returns the number of operands by operation group
  function automatic int unsigned num_operands(opgroup_e grp);
    unique case (grp)
      ADDMUL:  return 3;
      DIVSQRT: return 2;
      NONCOMP: return 2;
      CONV:    return 3; // vectorial casts use 3 operands
      default: return 0;
    endcase
  endfunction

  // Returns the number of lanes according to width, format and vectors
  function automatic int unsigned num_lanes(int unsigned width, fp_format_e fmt, logic vec);
    return vec ? width / fp_width(fmt) : 1; // if no vectors, only one lane
  endfunction

  // Returns the maximum number of lanes in the FPU according to width, format config and vectors
  function automatic int unsigned max_num_lanes(int unsigned width, fmt_logic_t cfg, logic vec);
    return vec ? width / min_fp_width(cfg) : 1; // if no vectors, only one lane
  endfunction

  // Returns a mask of active FP formats that are present in lane lane_no of a multiformat slice
  function automatic fmt_logic_t get_lane_formats(int unsigned width,
                                                  fmt_logic_t cfg,
                                                  int unsigned lane_no);
    automatic fmt_logic_t res;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      // Mask active formats with the number of lanes for that format
      res[fmt] = cfg[fmt] & (width / fp_width(fp_format_e'(fmt)) > lane_no);
    return res;
  endfunction

  // Returns a mask of active INT formats that are present in lane lane_no of a multiformat slice
  function automatic ifmt_logic_t get_lane_int_formats(int unsigned width,
                                                       fmt_logic_t cfg,
                                                       ifmt_logic_t icfg,
                                                       int unsigned lane_no);
    automatic ifmt_logic_t res;
    automatic fmt_logic_t lanefmts;
    res = '0;
    lanefmts = get_lane_formats(width, cfg, lane_no);

    for (int unsigned ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++)
      for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
        // Mask active int formats with the width of the float formats
        if ((fp_width(fp_format_e'(fmt)) == int_width(int_format_e'(ifmt))))
          res[ifmt] |= icfg[ifmt] && lanefmts[fmt];
    return res;
  endfunction

  // Returns a mask of active FP formats that are present in lane lane_no of a CONV slice
  function automatic fmt_logic_t get_conv_lane_formats(int unsigned width,
                                                       fmt_logic_t cfg,
                                                       int unsigned lane_no);
    automatic fmt_logic_t res;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      // Mask active formats with the number of lanes for that format, CPK at least twice
      res[fmt] = cfg[fmt] && ((width / fp_width(fp_format_e'(fmt)) > lane_no) ||
                             (CPK_FORMATS[fmt] && (lane_no < 2)));
    return res;
  endfunction

  // Returns a mask of active INT formats that are present in lane lane_no of a CONV slice
  function automatic ifmt_logic_t get_conv_lane_int_formats(int unsigned width,
                                                            fmt_logic_t cfg,
                                                            ifmt_logic_t icfg,
                                                            int unsigned lane_no);
    automatic ifmt_logic_t res;
    automatic fmt_logic_t lanefmts;
    res = '0;
    lanefmts = get_conv_lane_formats(width, cfg, lane_no);

    for (int unsigned ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++)
      for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
        // Mask active int formats with the width of the float formats
        res[ifmt] |= icfg[ifmt] && lanefmts[fmt] &&
                     (fp_width(fp_format_e'(fmt)) == int_width(int_format_e'(ifmt)));
    return res;
  endfunction

  // Return whether any active format is set as MERGED
  function automatic logic any_enabled_multi(fmt_unit_types_t types, fmt_logic_t cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i] && types[i] == MERGED)
        return 1'b1;
      return 1'b0;
  endfunction

  // Return whether the given format is the first active one set as MERGED
  function automatic logic is_first_enabled_multi(fp_format_e fmt,
                                                  fmt_unit_types_t types,
                                                  fmt_logic_t cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++) begin
      if (cfg[i] && types[i] == MERGED) return (fp_format_e'(i) == fmt);
    end
    return 1'b0;
  endfunction

  // Returns the first format that is active and is set as MERGED
  function automatic fp_format_e get_first_enabled_multi(fmt_unit_types_t types, fmt_logic_t cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i] && types[i] == MERGED)
        return fp_format_e'(i);
      return fp_format_e'(0);
  endfunction

  // Returns the largest number of regs that is active and is set as MERGED
  function automatic int unsigned get_num_regs_multi(fmt_unsigned_t regs,
                                                     fmt_unit_types_t types,
                                                     fmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++) begin
      if (cfg[i] && types[i] == MERGED) res = maximum(res, regs[i]);
    end
    return res;
  endfunction

endpackage


module fpnew_opgroup_block #(
  parameter fpnew_pkg::opgroup_e        OpGroup       = fpnew_pkg::ADDMUL,
  // FPU configuration
  parameter int unsigned                Width         = 32,
  parameter logic                       EnableVectors = 1'b1,
  parameter fpnew_pkg::fmt_logic_t      FpFmtMask     = '1,
  parameter fpnew_pkg::ifmt_logic_t     IntFmtMask    = '1,
  parameter fpnew_pkg::fmt_unsigned_t   FmtPipeRegs   = '{default: 0},
  parameter fpnew_pkg::fmt_unit_types_t FmtUnitTypes  = '{default: fpnew_pkg::PARALLEL},
  parameter fpnew_pkg::pipe_config_t    PipeConfig    = fpnew_pkg::BEFORE,
  parameter type                        TagType       = logic,
  // Do not change
  localparam int unsigned NUM_FORMATS  = fpnew_pkg::NUM_FP_FORMATS,
  localparam int unsigned NUM_OPERANDS = fpnew_pkg::num_operands(OpGroup)
			     ) ();

 for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_parallel_slices
    // Some constants for this format
    localparam logic ANY_MERGED = fpnew_pkg::any_enabled_multi(FmtUnitTypes, FpFmtMask);
    localparam logic IS_FIRST_MERGED =
        fpnew_pkg::is_first_enabled_multi(fpnew_pkg::fp_format_e'(fmt), FmtUnitTypes, FpFmtMask);
    localparam DEBUGME = FpFmtMask[fmt];

    // Generate slice only if format enabled
    if (FpFmtMask[fmt] && (FmtUnitTypes[fmt] == fpnew_pkg::PARALLEL)) begin : active_format

      logic in_valid;

      assign in_valid = in_valid_i & (dst_fmt_i == fmt); // enable selected format

      fpnew_opgroup_fmt_slice #(
        .OpGroup       ( OpGroup                      ),
        .FpFormat      ( fpnew_pkg::fp_format_e'(fmt) ),
        .Width         ( Width                        ),
        .EnableVectors ( EnableVectors                ),
        .NumPipeRegs   ( FmtPipeRegs[fmt]             ),
        .PipeConfig    ( PipeConfig                   ),
        .TagType       ( TagType                      )
      ) i_fmt_slice (
      );
       end
  end
   
endmodule


   
module fpnew_top #(
  // FPU configuration
  parameter fpnew_pkg::fpu_features_t       Features       = fpnew_pkg::RV64D_Xsflt,
  parameter fpnew_pkg::fpu_implementation_t Implementation = fpnew_pkg::DEFAULT_NOREGS,
  parameter type                            TagType        = logic,
  // Do not change
  localparam int unsigned WIDTH        = Features.Width,
  localparam int unsigned NUM_OPERANDS = 3
		   ) ();

  localparam int unsigned NUM_OPGROUPS = fpnew_pkg::NUM_OPGROUPS;
  localparam int unsigned NUM_FORMATS  = fpnew_pkg::NUM_FP_FORMATS;

   for (genvar opgrp = 0; opgrp < int'(NUM_OPGROUPS); opgrp++) begin : gen_operation_groups
    localparam int unsigned NUM_OPS = fpnew_pkg::num_operands(fpnew_pkg::opgroup_e'(opgrp));
      localparam DEBUGYOU = Implementation.UnitTypes[opgrp];
      
    fpnew_opgroup_block #(
      .OpGroup       ( fpnew_pkg::opgroup_e'(opgrp)    ),
      .Width         ( WIDTH                           ),
      .EnableVectors ( Features.EnableVectors          ),
      .FpFmtMask     ( Features.FpFmtMask              ),
      .IntFmtMask    ( Features.IntFmtMask             ),
      .FmtPipeRegs   ( Implementation.PipeRegs[opgrp]  ),
      .FmtUnitTypes  ( Implementation.UnitTypes[opgrp] ),
      .PipeConfig    ( Implementation.PipeConfig       ),
      .TagType       ( TagType                         )
    ) i_opgroup_block (
    );
  end



endmodule


module fpu_wrap import ariane_pkg::*; ();
  if (FP_PRESENT) begin : fpu_gen

localparam fpnew_pkg::fpu_features_t FPU_FEATURES = '{
      Width:         64,
      EnableVectors: ariane_pkg::XFVEC,
      EnableNanBox:  1'b1,
      FpFmtMask:     {RVF, RVD, XF16, XF8, XF16ALT},
      IntFmtMask:    {XFVEC && XF8, XFVEC && (XF16 || XF16ALT), 1'b1, 1'b1}
    };

localparam fpnew_pkg::fpu_implementation_t FPU_IMPLEMENTATION = '{
      PipeRegs:  '{// FP32, FP64, FP16, FP8, FP16alt
                 '{LAT_COMP_FP32, LAT_COMP_FP64, LAT_COMP_FP16, LAT_COMP_FP8, LAT_COMP_FP16ALT}, // ADDMUL
                 '{default: LAT_DIVSQRT}, // DIVSQRT
                 '{default: LAT_NONCOMP}, // NONCOMP
                 '{default: LAT_CONV}},   // CONV
      UnitTypes: '{'{default: fpnew_pkg::PARALLEL}, // ADDMUL
                   '{default: fpnew_pkg::MERGED},   // DIVSQRT
                   '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                   '{default: fpnew_pkg::MERGED}},  // CONV
      PipeConfig: fpnew_pkg::DISTRIBUTED
    };

     localparam DEBUGMOI = FPU_IMPLEMENTATION.UnitTypes[1];
     
     
      
       fpnew_top #(
      .Features       ( FPU_FEATURES              ),
      .Implementation ( FPU_IMPLEMENTATION        ),
      .TagType        ( logic [TRANS_ID_BITS-1:0] )
		   ) i_fpnew_bulk ();
     
  end

   
endmodule

module ex_stage import ariane_pkg::*; #(
    parameter int unsigned ASID_WIDTH = 1,
    parameter ariane_pkg::ariane_cfg_t ArianeCfg = ariane_pkg::ArianeDefaultConfig
					) ();

      generate
        if (FP_PRESENT) begin : fpu_gen
            fu_data_t fpu_data;
            assign fpu_data  = fpu_valid_i ? fu_data_i  : '0;

            fpu_wrap fpu_i (
                .clk_i,
                .rst_ni,
                .flush_i,
                .fpu_valid_i,
                .fpu_ready_o,
                .fu_data_i ( fpu_data ),
                .fpu_fmt_i,
                .fpu_rm_i,
                .fpu_frm_i,
                .fpu_prec_i,
                .fpu_trans_id_o,
                .result_o ( fpu_result_o ),
                .fpu_valid_o,
                .fpu_exception_o
            );
	end // block: fpu_gen
    endgenerate

	 
endmodule


module ariane import ariane_pkg::*; #(
  parameter ariane_pkg::ariane_cfg_t ArianeCfg     = ariane_pkg::ArianeDefaultConfig
				       ) ();
  ex_stage #(
    .ASID_WIDTH ( ASID_WIDTH ),
    .ArianeCfg  ( ArianeCfg  )
	     ) ex_stage_i ();

   
endmodule // ariane

module top();
    ariane #(
    .ArianeCfg  ( ariane_soc::ArianeSocCfg )
	     ) i_ariane ();

endmodule
