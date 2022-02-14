////////////////////////////////////////////////////////////////////////////////
// R5P: CSR package
////////////////////////////////////////////////////////////////////////////////
// Constants:
// CSR_*_RST - SCR * reset value
// CSR_*_WEM - CSR * write enable mask
////////////////////////////////////////////////////////////////////////////////
// Copyright 2022 Iztok Jeras
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
///////////////////////////////////////////////////////////////////////////////

package r5p_csr_pkg;

import riscv_isa_pkg::*;
import riscv_csr_pkg::*;

import r5p_pkg::*;

////////////////////////////////////////////////////////////////////////////////
// Machine-Level CSRs
////////////////////////////////////////////////////////////////////////////////

localparam csr_misa_t CSR_RST_MISA = '{
  MXL: XLEN_64,
  Extensions: '{
    M: '1,
    I: '1,
    C: '1,
    B: '0,
    A: '0,
    default: '0
  },
  default: '0
};
localparam csr_misa_t CSR_WEM_MISA = '0;

// Machine Vendor ID Register
// NOTE: JEDEC ID values are not assigned yet
localparam csr_mvendorid_t CSR_RST_MVENDORID = '{
   zero  : 32'h0000_0000,  // **:32 //
   Bank  : '0,             // 31:07 //
   Offset: '0              // 06:00 //
};
localparam csr_mvendorid_t CSR_WEM_MVENDORID = '{
   zero  : 32'h0000_0000,  // **:32 //
   Bank  : '0,             // 31:07 //
   Offset: '0              // 06:00 //
};

// Machine Architecture ID Register
localparam csr_marchid_t CSR_RST_MARCHID = MXLEN'(0);
localparam csr_marchid_t CSR_WEM_MARCHID = MXLEN'(0);

// Machine Implementation ID Register
localparam csr_mimpid_t CSR_RST_MIMPID = MXLEN'(0);
localparam csr_mimpid_t CSR_WEM_MIMPID = MXLEN'(0);

// Hart ID Register
localparam csr_mhartid_t CSR_RST_MHARTID = MXLEN'(0);
localparam csr_mhartid_t CSR_WEM_MHARTID = MXLEN'(0);

// Machine Status Register
localparam csr_mstatus_rv64_t CSR_RST_MSTATUS = '{
  SD  : 1'b0,           // SD=((FS==11) OR (XS==11)))
  // Endianness Control
  MBE : ENDIAN_LITTLE,  // M-mode endianness
  SBE : ENDIAN_LITTLE,  // S-mode endianness
  // Base ISA Control
  SXL : XLEN_64,        // S-mode XLEN
  UXL : XLEN_64,        // U-mode XLEN
  // Virtualization Support
  TSR : 1'b0,           // Trap SRET
  TW  : 1'b0,           // Timeout Wait
  TVM : 1'b0,           // Trap Virtual Memory
  // Memory Privilige
  MXR : 1'b0,           // Make eXecutable Readable
  SUM : 1'b0,           // permit Supervisor User Memory access
  MPRV: 1'b0,           // Modify PRiVilege
  // Extension Context Status
  XS  : CONTEXT_OFF,    // user-mode extensions context status
  FS  : CONTEXT_OFF,    // floating-point context status
  // Privilege and Global Interrupt-Enable Stack
  MPP : LVL_M,          // machine previous privilege mode
  SPP : 1'b0,           // supervisor previous privilege mode
  MPIE: 1'b0,           // machine interrupt-enable active prior to the trap
  UBE : ENDIAN_LITTLE,  // U-mode endianness
  SPIE: 1'b0,           // supervisor interrupt-enable active prior to the trap
  MIE : 1'b0,           // machine global interrupt-enable
  SIE : 1'b0,           // supervisor global interrupt-enable
  default: '0
};
localparam csr_mstatus_rv64_t CSR_WEM_MSTATUS = '{
  SD  :                1'b0,    // SD=((FS==11) OR (XS==11)))
  // Endianness Control
  MBE : csr_endian_t '(1'b0),   // M-mode endianness
  SBE : csr_endian_t '(1'b0),   // S-mode endianness
  // Base ISA Control
  SXL : csr_xlen_t   '(2'b00),  // S-mode XLEN
  UXL : csr_xlen_t   '(2'b00),  // U-mode XLEN
  // Virtualization Support
  TSR :                1'b0,    // Trap SRET
  TW  :                1'b0,    // Timeout Wait
  TVM :                1'b0,    // Trap Virtual Memory
  // Memory Privilige
  MXR :                1'b0,    // Make eXecutable Readable
  SUM :                1'b0,    // permit Supervisor User Memory access
  MPRV:                1'b0,    // Modify PRiVilege
  // Extension Context Status
  XS  : csr_context_t'(2'b00),  // user-mode extensions context status
  FS  : csr_context_t'(2'b00),  // floating-point context status
  // Privilege and Global Interrupt-Enable Stack
  MPP : isa_level_t  '(2'b00),  // machine previous privilege mode
  SPP :                1'b0,    // supervisor previous privilege mode
  MPIE:                1'b0,    // machine interrupt-enable active prior to the trap
  UBE : csr_endian_t '(1'b0),   // U-mode endianness
  SPIE:                1'b0,    // supervisor interrupt-enable active prior to the trap
  MIE :                1'b1,    // machine global interrupt-enable
  SIE :                1'b0,    // supervisor global interrupt-enable
  default: '0
};

// Machine Trap-Vector Base-Address Register
localparam csr_mtvec_t CSR_RST_MTVEC = '{
  BASE: '0,                // vector base address
  MODE: TVEC_MODE_DIRECT   // vector mode
};
localparam csr_mtvec_t CSR_WEM_MTVEC = '{
  BASE:                '1,     // vector base address
  MODE: csr_vector_t'(2'b01)   // vector mode (one bit is reserved)
};

//// Machine Exception Delegation Register
//typedef struct packed {
//  logic [MXLEN-1:0] Synchronous_Exceptions;
//} csr_medeleg_t;
//
//// Machine Interrupt Delegation Register
//typedef struct packed {
//  logic [MXLEN-1:0] Interrupts;
//} csr_mideleg_t;

// Machine Interrupt-Pending Register
localparam csr_mip_t CSR_RST_MIP = '{
  Interrupts: '0,    //
  MEIP      : 1'b0,  // machine-level external interrupt
  SEIP      : 1'b0,  // supervisor-level external interrupt
  MTIP      : 1'b0,  // machine-level timer interrupt
  STIP      : 1'b0,  // supervisor-level timer interrupt
  MSIP      : 1'b0,  // machine-level software interrupt
  SSIP      : 1'b0,  // supervisor-level software interrupt
  default: '0
};
localparam csr_mip_t CSR_WEM_MIP = '{
  Interrupts: '0,    //
  MEIP      : 1'b0,  // machine-level external interrupt
  SEIP      : 1'b0,  // supervisor-level external interrupt
  MTIP      : 1'b0,  // machine-level timer interrupt
  STIP      : 1'b0,  // supervisor-level timer interrupt
  MSIP      : 1'b0,  // machine-level software interrupt
  SSIP      : 1'b0,  // supervisor-level software interrupt
  default: '0
};

// Machine Interrupt-Enable Register
localparam csr_mie_t CSR_RST_MIE = '{
  Interrupts: '0,    //
  MEIE      : 1'b0,  // machine-level external interrupt
  SEIE      : 1'b0,  // supervisor-level external interrupt
  MTIE      : 1'b0,  // machine-level timer interrupt
  STIE      : 1'b0,  // supervisor-level timer interrupt
  MSIE      : 1'b0,  // machine-level software interrupt
  SSIE      : 1'b0,  // supervisor-level software interrupt
  default: '0
};
localparam csr_mie_t CSR_WEM_MIE = '{
  Interrupts: '0,    //
  MEIE      : 1'b0,  // machine-level external interrupt
  SEIE      : 1'b0,  // supervisor-level external interrupt
  MTIE      : 1'b0,  // machine-level timer interrupt
  STIE      : 1'b0,  // supervisor-level timer interrupt
  MSIE      : 1'b0,  // machine-level software interrupt
  SSIE      : 1'b0,  // supervisor-level software interrupt
  default: '0
};

// Hardware Performance Monitor
localparam csr_mhpmcounter_t CSR_RST_MHPMCOUNTER = '0;
localparam csr_mhpmcounter_t CSR_WEM_MHPMCOUNTER = '1;
localparam csr_mhpmevent_t CSR_RST_MHPMEVENT = '0;
localparam csr_mhpmevent_t CSR_WEM_MHPMEVENT = csr_mhpmevent_t'(r5p_hpmevent_t'('1));

// Machine Counter-Enable Register
localparam csr_mcounteren_t CSR_RST_MCOUNTEREN = '{
  HPM: '0,    // hpmcounter[*]
  IR : 1'b0,  // instret
  TM : 1'b0,  // time
  CY : 1'b0,  // cycle
  default: '0
};
localparam csr_mcounteren_t CSR_WEM_MCOUNTEREN = '{
  HPM: '1,    // hpmcounter[*]
  IR : 1'b1,  // instret
  TM : 1'b1,  // time
  CY : 1'b1,  // cycle
  default: '0
};

// Machine Counter-Inhibit Register
localparam csr_mcountinhibit_t CSR_RST_MCOUNTINHIBIT = '{
  HPM: '0,    // hpmcounter[*]
  IR : 1'b0,  // instret
//TM : 1'b0,  // time (always 1'b0)
  CY : 1'b0,  // cycle
  default: '0
};
localparam csr_mcountinhibit_t CSR_WEM_MCOUNTINHIBIT = '{
  HPM: '1,    // hpmcounter[*]
  IR : 1'b1,  // instret
//TM : 1'b0,  // time (always 1'b0)
  CY : 1'b1,  // cycle
  default: '0
};

// Machine Scratch Register
localparam csr_mscratch_t CSR_RST_MSCRATCH = '0;
localparam csr_mscratch_t CSR_WEM_MSCRATCH = '1;

// Machine Exception Program Counter
localparam csr_mepc_t CSR_RST_MEPC = '0;
localparam csr_mepc_t CSR_WEM_MEPC = '{epc: '1, default: '0};
// NOTE: if IALIGN=32, then 2 LSB bits are 1'b0

// Machine Cause Register
localparam csr_mcause_t CSR_RST_MCAUSE = '0;
localparam csr_mcause_t CSR_WEM_MCAUSE = '0;
// logic             Interrupt     ;  // set if the trap was caused by an interrupt
// logic [MXLEN-2:0] Exception_Code;  // code identifying the last exception or interrupt

//// Machine cause register (mcause) values after trap
//typedef enum csr_mcause_t {
//  // Interrupts
//  CAUSE_IRQ_RSV_0            = {1'b1, (MXLEN-1-6)'(0), 6'd00},  // Reserved
//  CAUSE_IRQ_SW_S             = {1'b1, (MXLEN-1-6)'(0), 6'd01},  // Supervisor software interrupt
//  CAUSE_IRQ_RSV_2            = {1'b1, (MXLEN-1-6)'(0), 6'd02},  // Reserved
//  CAUSE_IRQ_SW_M             = {1'b1, (MXLEN-1-6)'(0), 6'd03},  // Machine software interrupt
//  CAUSE_IRQ_RSV_4            = {1'b1, (MXLEN-1-6)'(0), 6'd04},  // Reserved
//  CAUSE_IRQ_TM_S             = {1'b1, (MXLEN-1-6)'(0), 6'd05},  // Supervisor timer interrupt
//  CAUSE_IRQ_RSV_6            = {1'b1, (MXLEN-1-6)'(0), 6'd06},  // Reserved
//  CAUSE_IRQ_TM_M             = {1'b1, (MXLEN-1-6)'(0), 6'd07},  // Machine timer interrupt
//  CAUSE_IRQ_RSV_8            = {1'b1, (MXLEN-1-6)'(0), 6'd08},  // Reserved
//  CAUSE_IRQ_EXT_S            = {1'b1, (MXLEN-1-6)'(0), 6'd09},  // Supervisor external interrupt
//  CAUSE_IRQ_RSV_10           = {1'b1, (MXLEN-1-6)'(0), 6'd10},  // Reserved
//  CAUSE_IRQ_EXT_M            = {1'b1, (MXLEN-1-6)'(0), 6'd11},  // Machine external interrupt
//  CAUSE_IRQ_RSV_12           = {1'b1, (MXLEN-1-6)'(0), 6'd12},  // Reserved
//  CAUSE_IRQ_RSV_13           = {1'b1, (MXLEN-1-6)'(0), 6'd13},  // Reserved
//  CAUSE_IRQ_RSV_14           = {1'b1, (MXLEN-1-6)'(0), 6'd14},  // Reserved
//  CAUSE_IRQ_RSV_15           = {1'b1, (MXLEN-1-6)'(0), 6'd15},  // Reserved
////                             {1'b1, (MXLEN-1-6)'(0),  >=16},  // Designated for platform use
//  // Exceptions
//  CAUSE_EXC_IFU_MISALIGNED   = {1'b0, (MXLEN-1-6)'(0), 6'd00},  // Instruction address misaligned
//  CAUSE_EXC_IFU_FAULT        = {1'b0, (MXLEN-1-6)'(0), 6'd01},  // Instruction access fault
//  CAUSE_EXC_IFU_ILLEGAL      = {1'b0, (MXLEN-1-6)'(0), 6'd02},  // Illegal instruction
//  CAUSE_EXC_OP_EBREAK        = {1'b0, (MXLEN-1-6)'(0), 6'd03},  // Breakpoint
//  CAUSE_EXC_LOAD_MISALIGNED  = {1'b0, (MXLEN-1-6)'(0), 6'd04},  // Load address misaligned
//  CAUSE_EXC_LOAD_FAULT       = {1'b0, (MXLEN-1-6)'(0), 6'd05},  // Load access fault
//  CAUSE_EXC_STORE_MISALIGNED = {1'b0, (MXLEN-1-6)'(0), 6'd06},  // Store/AMO address misaligned
//  CAUSE_EXC_STORE_FAULT      = {1'b0, (MXLEN-1-6)'(0), 6'd07},  // Store/AMO access fault
//  CAUSE_EXC_OP_UCALL         = {1'b0, (MXLEN-1-6)'(0), 6'd08},  // Environment call from U-mode
//  CAUSE_EXC_OP_SCALL         = {1'b0, (MXLEN-1-6)'(0), 6'd09},  // Environment call from S-mode
//  CAUSE_EXC_OP_RSV           = {1'b0, (MXLEN-1-6)'(0), 6'd10},  // Reserved
//  CAUSE_EXC_OP_MCALL         = {1'b0, (MXLEN-1-6)'(0), 6'd11},  // Environment call from M-mode
//  CAUSE_EXC_MMU_INST_FAULT   = {1'b0, (MXLEN-1-6)'(0), 6'd12},  // Instruction page fault
//  CAUSE_EXC_MMU_LOAD_FAULT   = {1'b0, (MXLEN-1-6)'(0), 6'd13},  // Load page fault
//  CAUSE_EXC_MMU_RSV          = {1'b0, (MXLEN-1-6)'(0), 6'd14},  // Reserved
//  CAUSE_EXC_MMU_STORE_FAULT  = {1'b0, (MXLEN-1-6)'(0), 6'd15}   // Store/AMO page fault
////CAUSE_EXC_16_23            = {1'b0, (MXLEN-1-6)'(0), 6'd??},  // Reserved
////CAUSE_EXC_24_31            = {1'b0, (MXLEN-1-6)'(0), 6'd??},  // Designated for custom use
////CAUSE_EXC_32_47            = {1'b0, (MXLEN-1-6)'(0), 6'd??},  // Reserved
////CAUSE_EXC_48_63            = {1'b0, (MXLEN-1-6)'(0), 6'd??},  // Designated for custom use
////CAUSE_EXC_**_64            = {1'b0, (MXLEN-1-6)'(0), 6'd??},  // Reserved
//} csr_cause_t;

// Machine Trap Value Register
localparam csr_mtval_t CSR_RST_MTVAL = '0;
localparam csr_mtval_t CSR_WEM_MTVAL = '0;

///////////////////////////////////////////////////////////////////////////////
// CSR reset values
///////////////////////////////////////////////////////////////////////////////

localparam csr_map_st CSR_RST_S = '{
  mstatus       :            CSR_RST_MSTATUS       ,  // 0x300       // Machine status register.
  misa          :            CSR_RST_MISA          ,  // 0x301       // ISA and extensions
  mie           :            CSR_RST_MIE           ,  // 0x304       // Machine interrupt-enable register.
  mtvec         :            CSR_RST_MTVEC         ,  // 0x305       // Machine trap-handler base address.
  mcounteren    :            CSR_RST_MCOUNTEREN    ,  // 0x306       // Machine counter enable.
  mcountinhibit :            CSR_RST_MCOUNTINHIBIT ,  // 0x320       // Machine counter-inhibit register.
  mscratch      :            CSR_RST_MSCRATCH      ,  // 0x340       // Scratch register for machine trap handlers.
  mepc          :            CSR_RST_MEPC          ,  // 0x341       // Machine exception program counter.
  mcause        :            CSR_RST_MCAUSE        ,  // 0x342       // Machine trap cause.
  mtval         :            CSR_RST_MTVAL         ,  // 0x343       // Machine bad address or instruction.
  mip           :            CSR_RST_MIP           ,  // 0x344       // Machine interrupt pending.
  mhpmcounter   : '{default: CSR_RST_MHPMCOUNTER  },  // 0xB03:0xB1f // Machine performance-monitoring counter.
  mhpmevent     : '{default: CSR_RST_MHPMEVENT    },  // 0x323:0x33F // Machine performance-monitoring event selector.
  mvendorid     :            CSR_RST_MVENDORID     ,  // 0xF11       // Vendor ID.
  marchid       :            CSR_RST_MARCHID       ,  // 0xF12       // Architecture ID.
  mimpid        :            CSR_RST_MIMPID        ,  // 0xF13       // Implementation ID.
  mhartid       :            CSR_RST_MHARTID       ,  // 0xF14       // Hardware thread ID.
  /* verilator lint_off WIDTHCONCAT */
  default    : '0
  /* verilator lint_on WIDTHCONCAT */
};

localparam csr_map_ut CSR_RST = CSR_RST_S;

///////////////////////////////////////////////////////////////////////////////
// CSR write enable mask
///////////////////////////////////////////////////////////////////////////////

localparam csr_map_st CSR_WEM_S = '{
  mstatus       :            CSR_WEM_MSTATUS       ,  // 0x300       // Machine status register.
  misa          :            CSR_WEM_MISA          ,  // 0x301       // ISA and extensions
  mie           :            CSR_WEM_MIE           ,  // 0x304       // Machine interrupt-enable register.
  mtvec         :            CSR_WEM_MTVEC         ,  // 0x305       // Machine trap-handler base address.
  mcounteren    :            CSR_WEM_MCOUNTEREN    ,  // 0x306       // Machine counter enable.
  mcountinhibit :            CSR_WEM_MCOUNTINHIBIT ,  // 0x320       // Machine counter-inhibit register.
  mscratch      :            CSR_WEM_MSCRATCH      ,  // 0x340       // Scratch register for machine trap handlers.
  mepc          :            CSR_WEM_MEPC          ,  // 0x341       // Machine exception program counter.
  mcause        :            CSR_WEM_MCAUSE        ,  // 0x342       // Machine trap cause.
  mtval         :            CSR_WEM_MTVAL         ,  // 0x343       // Machine bad address or instruction.
  mip           :            CSR_WEM_MIP           ,  // 0x344       // Machine interrupt pending.
  mhpmcounter   : '{default: CSR_WEM_MHPMCOUNTER  },  // 0xB03:0xB1f // Machine performance-monitoring counter.
  mhpmevent     : '{default: CSR_WEM_MHPMEVENT    },  // 0x323:0x33F // Machine performance-monitoring event selector.
  mvendorid     :            CSR_WEM_MVENDORID     ,  // 0xF11       // Vendor ID.
  marchid       :            CSR_WEM_MARCHID       ,  // 0xF12       // Architecture ID.
  mimpid        :            CSR_WEM_MIMPID        ,  // 0xF13       // Implementation ID.
  mhartid       :            CSR_WEM_MHARTID       ,  // 0xF14       // Hardware thread ID.
  /* verilator lint_off WIDTHCONCAT */
  default    : '0
  /* verilator lint_on WIDTHCONCAT */
};

localparam csr_map_ut CSR_WEM = CSR_WEM_S;

endpackage: r5p_csr_pkg