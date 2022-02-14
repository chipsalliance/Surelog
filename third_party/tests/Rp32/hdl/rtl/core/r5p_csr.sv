///////////////////////////////////////////////////////////////////////////////
// R5P: control/status registers
///////////////////////////////////////////////////////////////////////////////
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

import riscv_isa_pkg::*;
import riscv_csr_pkg::*;

import r5p_pkg::*;
import r5p_csr_pkg::*;

module r5p_csr #(
  // RISC-V ISA
  int unsigned     XLEN = 32
)(
  // system signals
  input  logic            clk,  // clock
  input  logic            rst,  // reset
  // CSR address map union output
  output csr_map_ut       csr_map,
  // CSR control and data input/output
  input  ctl_csr_t        csr_ctl,  // CSR instruction control structure
  input  logic [XLEN-1:0] csr_wdt,  // write data from GPR
  output logic [XLEN-1:0] csr_rdt,  // read  data to   GPR
  // trap handler
  input  ctl_priv_t       priv_i,  // privileged instruction control structure
  input  logic            trap_i,  // 
  input  logic [XLEN-1:0] epc_i ,  // PC increment
  output logic [XLEN-1:0] epc_o ,  // exception program counter
  output logic [XLEN-1:0] tvec_o,  // trap vector
  // hardware performance monitor
  input  r5p_hpmevent_t   event_i
  // TODO: debugger, ...
);

///////////////////////////////////////////////////////////////////////////////
// current privilege level
///////////////////////////////////////////////////////////////////////////////

// NOTE: the current privelege level is not visible by reading any CSR
//       software code itself must be aware of the privelege level it is running in
isa_level_t level;

///////////////////////////////////////////////////////////////////////////////
// CSR Address Mapping Conventions
///////////////////////////////////////////////////////////////////////////////

// convention signals
logic cnv_aen;  // access enable  (depends on register address range)
logic cnv_ren;  // read   enable
logic cnv_wen;  // write  enable  (depends on register address range)

// convention access enable
//   Access is enabled if the level in the CSR address
//   is lower or equal to the current privilege level.
assign cnv_aen = csr_ctl.adr.level <= level;

// convention read/write enable
//   Read access has no additional limitations.
//   Write access is further limited to `ACCESS_RW[012]` segments of the CSR address space.
assign cnv_ren = cnv_aen;
assign cnv_wen = cnv_aen & (csr_ctl.adr.perm != ACCESS_RO3);

logic csr_ren;  // read   enable
logic csr_wen;  // write  enable  (depends on register address range)

// CSR read/write enable
// Depends on Zicsr instruction decoder and CSR Address Mapping Conventions)
assign csr_ren = csr_ctl.ren & cnv_ren;
assign csr_wen = csr_ctl.wen & cnv_wen;

// TODO: define access error conditions triggering illegal instruction

// CSR access illegal function
function logic [XLEN-1:0] csr_ill_f (
  logic [XLEN-1:0] csr_rdt
);
endfunction: csr_ill_f

///////////////////////////////////////////////////////////////////////////////
// CSR data constructs
///////////////////////////////////////////////////////////////////////////////

// CSR data mask
logic [XLEN-1:0] csr_msk;

// CSR data mask decoder
always_comb begin
  unique case (csr_ctl.msk)
    CSR_REG: csr_msk = csr_wdt;             // GPR register source 1
    CSR_IMM: csr_msk = XLEN'(csr_ctl.imm);  // 5-bit zero extended immediate
    default: csr_msk = 'x;
  endcase
end

// CSR write mask function
function logic [XLEN-1:0] csr_wdt_f (
  logic [XLEN-1:0] csr_rdt
);
  unique casez (csr_ctl.op)
    CSR_RW : csr_wdt_f =            csr_msk;  // write mask bits
    CSR_SET: csr_wdt_f = csr_rdt |  csr_msk;  // set   mask bits
    CSR_CLR: csr_wdt_f = csr_rdt & ~csr_msk;  // clear mask bits
    default: begin end
  endcase
endfunction: csr_wdt_f

///////////////////////////////////////////////////////////////////////////////
// helper functions
///////////////////////////////////////////////////////////////////////////////

// *CAUSE
// TODO: extend with missing causes
function csr_mcause_t cause_f (
  ctl_priv_t  priv,
  isa_level_t level
);
  unique casez (priv_i.typ)
    PRIV_EBREAK: cause_f = CAUSE_EXC_OP_EBREAK;
    PRIV_ECALL : unique case (level)
      LVL_U: cause_f = CAUSE_EXC_OP_UCALL;  // Environment call from U-mode
      LVL_S: cause_f = CAUSE_EXC_OP_SCALL;  // Environment call from S-mode
      LVL_R: cause_f = CAUSE_EXC_OP_RSV  ;  // Reserved
      LVL_M: cause_f = CAUSE_EXC_OP_MCALL;  // Environment call from M-mode
    endcase
    default: cause_f = 'x;
  endcase
endfunction: cause_f

csr_mcause_t cause;
assign cause = cause_f(priv_i, level);

// trap delegation
logic [XLEN-1:0] deleg;
assign deleg = cause.Interrupt ? csr_map.s.mideleg : csr_map.s.medeleg;

// TVEC address calculator
function logic [XLEN-1:0] tvec_f (
  csr_mtvec_t  tvec,
  csr_mcause_t cause
);
  unique case (tvec.MODE)
    TVEC_MODE_DIRECT  : tvec_f = {tvec.BASE, 2'b00};
    TVEC_MODE_VECTORED: tvec_f = {tvec.BASE + 4 * cause[6-1:0], 2'b00};
    default           : tvec_f = 'x;
  endcase
endfunction: tvec_f

///////////////////////////////////////////////////////////////////////////////
// read/write access
///////////////////////////////////////////////////////////////////////////////

// read access
assign csr_rdt = csr_ren ? csr_map.a[csr_ctl.adr] : '0;

// write access (CSR operation decoder)
always_ff @(posedge clk, posedge rst)
if (rst) begin
  // system starts in machine privilege level
  level <= LVL_M;
  // NOTE: a direct union to union (or struct to struct) assignment triggered some Verilator bug
  //   csr_map <= CSR_RST;  // this is triggering a verilator bug
  for (int unsigned i=0; i<2**12; i++) begin: reset
    csr_map.a[i] <= CSR_RST.a[i];
  end: reset
  // individual registers reset values are overriden
//  csr_map.s.misa      <= csr_misa_f(ISA);
//  csr_map.s.mtvec     <= MTVEC;
end else begin

// TODO:
// mstatus
// mtval on ebreak to PC?

  // trap handler
  if (trap_i) begin
    if (deleg[cause[$clog2(XLEN)-1:0]]) begin
      // delegate to S mode
      level <= LVL_S;
      csr_map.s.sepc   <= epc_i;
      csr_map.s.scause <= cause_f(priv_i, level);
    end else begin
      level            <= LVL_M;
      csr_map.s.mepc   <= epc_i;
      csr_map.s.mcause <= cause_f(priv_i, level);
    end
  end else begin
    // Zicsr access
    if (csr_wen) begin
      unique casez (csr_ctl.op)
        CSR_RW : csr_map.a[csr_ctl.adr] <=            csr_wdt;  // read/write
        CSR_SET: csr_map.a[csr_ctl.adr] <= csr_rdt |  csr_msk;  // set   masked bits
        CSR_CLR: csr_map.a[csr_ctl.adr] <= csr_rdt & ~csr_msk;  // clear masked bits
        default: begin end
      endcase
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // machine hardware performance monitor
  ///////////////////////////////////////////////////////////////////////////////
  
  // machine cycle counter
  if (csr_wen & (csr_ctl.adr == csr__mcycle)) begin
    csr_map.s.mcycle <= csr_wdt_f(csr_map.s.mcycle);
  end else begin
    if (~csr_map.s.mcountinhibit.CY & event_i.cycle)  csr_map.s.mcycle <= csr_map.s.mcycle + 1;
  end
  // machine instruction-retired counter
  if (csr_wen & (csr_ctl.adr == csr__minstret)) begin
    csr_map.s.minstret <= csr_wdt_f(csr_map.s.minstret);
  end else begin
    if (~csr_map.s.mcountinhibit.IR & event_i.instret)  csr_map.s.minstret <= csr_map.s.minstret + 1;
  end
  // machine performance monitor counter
  for (bit [12-1:0] i=3; i<=31; i++) begin
    if (csr_wen & (csr_ctl.adr == csr_dec_t'(csr__mhpmcounter3+i-12'd3))) begin
      csr_map.s.mhpmcounter[i] <= csr_wdt_f(csr_map.s.mhpmcounter[i]);
    end else begin
      if (~csr_map.s.mcountinhibit.HPM[i] & |(XLEN'(event_i) & csr_map.s.mhpmevent[i]))  csr_map.s.mhpmcounter[i] <= csr_map.s.mhpmcounter[i] + 1;
    end
  end
end

// TVEC (trap-vector address) and EPC (machine exception program counter)
// depend on 
always_comb begin
  unique case (level)
    LVL_U:  begin  tvec_o = tvec_f(csr_map.s.utvec, csr_map.s.ucause);  epc_o = csr_map.s.uepc;  end  // User/Application
    LVL_S:  begin  tvec_o = tvec_f(csr_map.s.stvec, csr_map.s.scause);  epc_o = csr_map.s.sepc;  end  // Supervisor
    LVL_R:  begin  tvec_o = 'x                                       ;  epc_o = 'x            ;  end  // Reserved
    LVL_M:  begin  tvec_o = tvec_f(csr_map.s.mtvec, csr_map.s.mcause);  epc_o = csr_map.s.mepc;  end  // Machine
  //default:begin  tvec_o = 'x                                       ;  epc_o = 'x            ;  end  // Reserved
  endcase
end

// 

endmodule: r5p_csr