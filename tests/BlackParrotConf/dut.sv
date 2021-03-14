
package bp_common_pkg;

  





// maps 1 --> 1 instead of to 0




// calculate ceil(x/y) 
















// using C-style shifts instead of a[i] allows the parameter of BSG_GET_BIT to be a parameter subrange                                                                                                                                                                               
// e.g., parameter[4:1][1], which DC 2016.12 does not allow                                                                                                                                                                                                                          



// This version of countones works in synthesis, but only up to 64 bits                                                                                                                                                                                                              
// we do a funny thing where we propagate X's in simulation if it is more than 64 bits                                                                                                                                                                                               
// and in synthesis, go ahead and ignore the high bits                                                                                                                                                                      









// nullify rpgroups






  


/*
 * This macro allows users to log to different mediums depending on a parameter
 *   print_type_mp - The different outputs as a bitmask
 *     0 - stdout ($display without newline)
 *     1 - file
 *   file_mp - The name of the log file, optional if using stdout
 *   str_mp - This is the format string for the print statement. Must be enclosed in parentheses
 *
 * Example usage -     
 *  `BP_LOG(0, `BP_LOG_STDOUT, ("I'm a display log %d", 2));
 *  `BP_LOG(file, `BP_LOG_FILE, ("I'm a file log %d %d", 1, 2));
 *  `BP_LOG(file, `BP_LOG_STDOUT | `BP_LOG_FILE, ("I'm both! %d", 3));
 *  `BP_LOG(0, `BP_LOG_NONE, ("I'm neither %d", 4));
 *
 * In practice, we expect users will set the log level as a module parameter rather than in the
 *   macro.
 * An obvious enhancement is to add log levels to control verbosity. A less obvious enhancement is 
 *   to support ordering of logs through a parameter. Perhaps #``delay_mp`` 
 */
localparam bp_log_none_gp   = 0;
localparam bp_log_stdout_gp = 1;
localparam bp_log_file_gp   = 2;










  /**
 *
 * bp_common_fe_be_if.vh
 *
 * bp_fe_be_interface.vh declares the interface between the BlackParrot Front End
 * and Back End For simplicity and flexibility, these signals are declared as
 * parameterizable structures. Each structure declares its width separately to
 * avoid preprocessor ordering issues.
 *
 * Logically, the BE controls the FE and may command the FE to flush all the states,
 * redirect the PC, etc. The FE uses its queue to supply the BE with (possibly
 * speculative) instruction/PC pairs and inform the BE of any exceptions that have
 * occurred within the unit (e.g., misaligned instruction fetch) so the BE may
 * ensure all exceptions are taken precisely.  The BE checks the PC in the
 * instruction/PC pairs to make sure that the FE predictions correspond to
 * correct architectural execution.
 *
 * NOTE: VCS can only handle packed unions where each member is the same size. Therefore, we
 *         need to do some macro hacking to get parameterized unions to work nicely.
 * NOTE: Potentially could make sense to separate two unidirectional interface files. This one
 *         is a little overwhelming.
 */






/*
 * Clients need only use this macro to declare all parameterized structs for FE<->BE interface.
 */



























































































































































































/*
 * Declare all fe-be widths at once as localparams
 */








/*
 * bp_fe_queue_s can either contain an instruction or exception.
 * bp_fe_queue_type_e specifies which information it contains.
 */
typedef enum bit
{
  e_fe_fetch       = 0
  ,e_fe_exception  = 1
} bp_fe_queue_type_e;

/*
 * bp_fe_command_queue_opcodes_e defines the opcodes from backend to frontend in
 * the cases of an exception. bp_fe_command_queue_opcodes_e explains the reason
 * of why pc is redirected.
 * e_op_state_reset is used after the reset, which flushes all the states.
 * e_op_pc_redirection defines the changes of PC, which happens during the branches.
 * e_op_icache_fence happens when there is flush in the icache.
 * e_op_attaboy informs the frontend that the prediction is correct.
 * e_op_itlb_fill_response happens when itlb populates translation.
 * e_op_itlb_fence issues a fence operation to itlb.
 */
typedef enum bit [2:0]
{
  e_op_state_reset         = 0
  ,e_op_pc_redirection     = 1
  ,e_op_interrupt          = 2
  ,e_op_icache_fence       = 3
  ,e_op_attaboy            = 4
  ,e_op_itlb_fill_response = 5
  ,e_op_itlb_fence         = 6
} bp_fe_command_queue_opcodes_e;

/*
 * bp_fe_misprediction_reason_e is the misprediction reason provided by the backend.
 */
typedef enum bit
{
  e_incorrect_prediction = 0
  ,e_not_a_branch        = 1
} bp_fe_misprediction_reason_e;

/*
 * The exception code types. e_instr_addr_misaligned is when the instruction
 * addresses are not aligned. e_itlb_miss is when the instruction has a miss in
 * the iTLB. ITLB misses can cause the instruction misaligned. Thus the frontend
 * detects the instruction miss first and then detect whether there is an ITLB
 * miss. e_instruction_access_fault is when the access control is violated.
 * e_illegal_instruction is when the instruction is not legitimate.
 */
typedef enum bit [1:0]
{
  e_instr_misaligned    = 0
  ,e_itlb_miss          = 1
  ,e_instr_access_fault = 2
  ,e_illegal_instr      = 3
} bp_fe_exception_code_e;

/*
 * bp_fe_command_queue_subopcodes_e defines the subopcodes in the case of pc_redirection in
 * bp_fe_command_queue_opcodes_e. It provides the reasons of why pc are redirected.
 * e_subop_uret,sret,mret are the returns from trap and contain the pc where it returns.
 * e_subop_interrupt is no-fault pc redirection.
 * e_subop_branch_mispredict is at-fault PC redirection.
 * e_subop_trap is at-fault PC redirection. It will changes the permission bits.
 * e_subop_context_switch is no-fault PC redirection. It redirect pc to a new address space.
*/
typedef enum bit [2:0]
{
  e_subop_uret
  ,e_subop_sret
  ,e_subop_mret
  ,e_subop_interrupt
  ,e_subop_branch_mispredict
  ,e_subop_trap
  ,e_subop_context_switch
} bp_fe_command_queue_subopcodes_e;

/* Declare width macros so that clients can use structs in ports before struct declaration */



































/* Ensure all members of packed unions have the same size. If parameterized unions are desired,
 * examine this code carefully. Else, clients should not have to use these macros
 */


































































  /**
 * bp_common_me_if.vh
 *
 * This file defines the interface between the CCEs and LCEs, and the CCEs and memory in the
 * BlackParrot coherence system. For ease of reuse and flexiblity, this interface is defined as a
 * collection of parameterized structs.
 *
 */






/*
 *
 * LCE-CCE Interface
 *
 * The following enums and structs define the LCE-CCE Interface within a BlackParrot coherence
 * system.
 *
 * There are 5 logical networks/message types:
 * 1. LCE Request
 * 2. LCE Response
 * 3. LCE Data Response
 * 4. LCE Command
 * 5. LCE Data Command
 *
 * These five logical message types are carried on three networks:
 * 1. Request (low priority)
 * 2. Command (medium priority), LCE Commands and Data Commands
 * 3. Response (high priority), LCE Responses and Data Responses
 *
 * A Request message may cause a Command message, and a Command message may cause a Response.
 * A higher priority message may not cause a lower priority message to be sent, which avoids
 * a circular dependency between message classes.
 *
 * LCE Request Processing Flow:
 *  At a high level, a cache miss is handled by an LCE Request being sent to the CCE, followed by
 *  a series of commands and and responses that handle invalidating, evicting, and writing-back
 *  blocks as needed, sending data and tags to the LCE, and concluding with the LCE sending a response
 *  to the CCE managing the transaction. The length of a coherence transaction depends on the type of
 *  request (read- or write-miss), the current state of the requested block, and the current state of
 *  the cache way that the miss will be filled into.
 *
 *
 * Clients should use the declare_bp_me_if() macro to declare all of the interface structs at once.
 *
 */


/* TODO list

1. Align cache block data fields in Command and Response messages to physical network flit boundary

*/


/*
 * 
 * LCE-CCE Interface Macro
 *
 * This macro defines all of the lce-cce interface stucts and port widths at once as localparams
 *
 */



























































































































/*
 * LCE-CCE Interface Enums
 *
 * These enums define the options for fields of the LCE-CCE Interface messages. Clients should use
 * the enums to set and compare fields of messages, rather than examining the bit pattern directly.
 */

/*
 * bp_lce_cce_req_type_e specifies whether the containing message is related to a read or write
 * cache miss request from and LCE.
 */
typedef enum bit [2:0]
{
  e_lce_req_type_rd         = 3'b000 // Read-miss
  ,e_lce_req_type_wr        = 3'b001 // Write-miss
  ,e_lce_req_type_uc_rd     = 3'b010 // Uncached Read-miss
  ,e_lce_req_type_uc_wr     = 3'b011 // Uncached Write-miss
  // 3'b100 - 3'b111 reserved / custom
} bp_lce_cce_req_type_e;


/*
 * bp_lce_cce_req_non_excl_e specifies whether the requesting LCE would like a read-miss request
 * to be returned in an exclusive coherence state if possible or not. An I$, for example, should
 * set this bit to indicate that there is no benefit in the CCE granting a cache block in the E
 * state as opposed to the S state in a MESI protocol. The CCE treats this bit as a hint, and is
 * not required to follow it.
 */
typedef enum bit 
{
  e_lce_req_excl            = 1'b0 // exclusive cache line request (read-only, exclusive request)
  ,e_lce_req_non_excl       = 1'b1 // non-exclusive cache line request (read-only, shared request)
} bp_lce_cce_req_non_excl_e;


/*
 * bp_lce_cce_lru_dirty_e specifies whether the LRU way in an LCE request (bp_lce_cce_req_s)
 * contains a dirty cache block. The 
 */
typedef enum bit 
{
  e_lce_req_lru_clean       = 1'b0 // lru way from requesting lce's tag set is clean
  ,e_lce_req_lru_dirty      = 1'b1 // lru way from requesting lce's tag set is dirty
} bp_lce_cce_lru_dirty_e;

/*
 * bp_lce_cce_uc_req_size_e defines the size of a uncached load or store request, in bytes.
 *
 */
typedef enum bit [1:0]
{
  e_lce_uc_req_1  = 2'b00
  ,e_lce_uc_req_2 = 2'b01
  ,e_lce_uc_req_4 = 2'b10
  ,e_lce_uc_req_8 = 2'b11
} bp_lce_cce_uc_req_size_e;

/*
 * bp_cce_coh_states_e defines the coherence states available in BlackParrot. Each bit represents
 * a property of the cache block as defined below:
 * 0: Shared (not Exclusive)
 * 1: Owned
 * 2: Potentially Dirty
 *
 * These properties are derived from "A Primer on Memory Consistency and Cache Coherence", and
 * they allow an easy definition for the common MOESIF coherence states.
 */
typedef enum bit [2:0] 
{
  e_COH_I                   = 3'b000 // Invalid
  ,e_COH_S                  = 3'b001 // Shared - clean, not owned, shared (not exclusive)
  ,e_COH_E                  = 3'b010 // Exclusive - clean, owned, not shared (exclusive)
  ,e_COH_F                  = 3'b011 // Forward - clean, owned, shared (not exclusive)
  // unused                 = 3'b100 // potentially dirty, not owned, not shared (exclusive)
  // unused                 = 3'b101 // potentially dirty, not owned, shared (not exclusive)
  ,e_COH_M                  = 3'b110 // Modified - potentially dirty, owned, not shared (exclusive)
  ,e_COH_O                  = 3'b111 // Owned - potentially dirty, owned, shared (not exclusive)
} bp_coh_states_e;







/*
 * bp_cce_lce_cmd_type_e defines the various commands that an CCE may issue to an LCE
 * e_lce_cmd_sync is used at the end of reset to direct the LCE to inform the CCE it is ready
 * e_lce_cmd_set_clear is sent by the CCE to invalidate an entire cache set in the LCE
 * e_lce_cmd_transfer is sent to command an LCE to transfer an entire cache block to another LCE
 * e_lce_cmd_set_tag is sent to update the tag and coherence state of a single cache line
 * e_lce_cmd_set_tag_wakeup is the same as e_lce_cmd_set_tag, plus it tells the LCE to wake up
 *   and resume normal execution. This is sent only when the CCE detects a write-miss request
 *   is actually an upgrade request.
 * e_lce_cmd_invalidate_tag is sent to invalidate a single cache entry. This command results in
 *   the coherence state of the specified entry being changed to Invalid (no read or write
 *   permissions)
 */
typedef enum bit [3:0] 
{
  e_lce_cmd_sync             = 4'b0000
  ,e_lce_cmd_set_clear       = 4'b0001
  ,e_lce_cmd_transfer        = 4'b0010
  ,e_lce_cmd_writeback       = 4'b0011
  ,e_lce_cmd_set_tag         = 4'b0100
  ,e_lce_cmd_set_tag_wakeup  = 4'b0101
  ,e_lce_cmd_invalidate_tag  = 4'b0110
  ,e_lce_cmd_uc_st_done      = 4'b0111
  ,e_lce_cmd_data            = 4'b1000 // cache block data to LCE, i.e., cache block fill
  ,e_lce_cmd_uc_data         = 4'b1001 // unached data to LCE, i.e, up to 64-bits data
  // 4'b1000 - 4'b1111 reserved / custom
} bp_lce_cmd_type_e;

/* bp_lce_cce_resp_type_e defines the different LCE-CCE response messages
 * e_lce_cce_sync_ack acknowledges receipt and processing of a Sync command
 * e_lce_cce_inv_ack acknowledges that an LCE has processed an Invalidation command
 * e_lce_cce_coh_ack acknowledges than an LCE has received both a set tag command AND a data
 *   command, or a set tag and wakeup command from the CCE. The sending LCE considers itself woken
 *   up after sending this ACK.
 * e_lce_resp_wb indicates the data field (cache block data) is valid, and that the LCE ahd the
 *   cache block in a dirty state
 * e_lce_resp_null_wb indicates that the LCE never wrote to the cache block and the block is still
 *   clean. The data field should be 0 and is invalid.
 */
typedef enum bit [2:0] 
{
  e_lce_cce_sync_ack         = 3'b000
  ,e_lce_cce_inv_ack         = 3'b001
  ,e_lce_cce_coh_ack         = 3'b010
  ,e_lce_cce_resp_wb         = 3'b011 // Normal Writeback Response (full data)
  ,e_lce_cce_resp_null_wb    = 3'b100 // Null Writeback Response (no data)
  // 3'b101 - 3'b111 reserved / custom
} bp_lce_cce_resp_type_e;

/*
 * Width macros for packed unions. Clients should not need to modify or use these.
 */

























/*
 * Width macros for LCE-CCE Message Networks
 */


































  /*
   * RV64 specifies a 64b effective address and 32b instruction.
   * BlackParrot supports SV39 virtual memory, which specifies 39b virtual / 56b physical address.
   * Effective addresses must have bits 39-63 match bit 38 
   *   or a page fault exception will occur during translation.
   * Currently, we only support a very limited number of parameter configurations.
   * Thought: We could have a `define surrounding core instantiations of each parameter and then
   * when they import this package, `declare the if structs. No more casting!
   */

  localparam bp_eaddr_width_gp = 64;
  localparam bp_instr_width_gp = 32;

  parameter bp_sv39_page_table_depth_gp = 3;
  parameter bp_sv39_pte_width_gp = 64;
  parameter bp_sv39_vaddr_width_gp = 39;
  parameter bp_sv39_paddr_width_gp = 56;
  parameter bp_sv39_ppn_width_gp = 44;
  parameter bp_page_size_in_bytes_gp = 4096;
  parameter bp_page_offset_width_gp = ( ((bp_page_size_in_bytes_gp)==1) ? 1 : $clog2((bp_page_size_in_bytes_gp)));

  parameter bp_data_resp_num_flit_gp = 4;
  parameter bp_data_cmd_num_flit_gp = 4;
 
  localparam dram_base_addr_gp         = 32'h8000_0000;
 
  localparam cfg_link_dev_base_addr_gp = 32'h01??_????;
  localparam clint_dev_base_addr_gp    = 32'h02??_????;
  localparam host_dev_base_addr_gp     = 32'h03??_????;
  localparam plic_dev_base_addr_gp     = 32'h0c??_????;
  
  localparam mipi_reg_base_addr_gp     = 32'h0200_0???;
  localparam mtimecmp_reg_base_addr_gp = 32'h0200_4???;
  localparam mtime_reg_addr_gp         = 32'h0200_bff8;
  localparam plic_reg_base_addr_gp     = 32'h0c00_0???;

endpackage : bp_common_pkg

package bp_common_rv64_pkg;

  /**
 *
 * bp_common_rv_defines.v
 * Based off of: https://bitbucket.org/taylor-bsg/bsg_manycore/src/master
 *                                           /v/vanilla_bean/parameters.v
 * TODO: Make opcodes into an enum, same with CSR defines
 */




/* RISCV definitions */















// Some useful RV64 instruction macros





// RV64 Immediate sign extension macros


















































































  









































































































































































typedef struct packed
{
  // Base address for traps
  logic [61:0] base;
  // Trap Mode
  //   00 - Direct, all exceptions set pc to BASE
  //   01 - Vectored, interrupts set pc to BASE+4xcause
  logic [1:0]  mode;
}  rv64_stvec_s;

typedef struct packed
{
  logic [38:0] base;
}  bp_stvec_s;











typedef struct packed
{
  logic [31:3] hpm;
  logic        ir;
  logic        cy;
}  rv64_scounteren_s;

typedef struct packed
{
  logic ir;
  logic cy;
}  bp_scounteren_s;














typedef logic [63:0] rv64_sscratch_s;
typedef logic [63:0] bp_sscratch_s;







typedef logic [63:0] rv64_sepc_s;
typedef logic [38:0] bp_sepc_s;









typedef struct packed
{
  logic        _interrupt;
  logic [62:0] ecode;
}  rv64_scause_s;

typedef struct packed
{
  logic       _interrupt;
  logic [3:0] ecode;
}  bp_scause_s;











typedef logic [63:0] rv64_stval_s;
typedef logic [38:0] bp_stval_s;







typedef struct packed
{
  // Translation Mode
  //   0000 - No Translation
  //   1000 - SV39
  //   1001 - SV48
  //   Others reserved
  logic [3:0] mode;
  logic [15:0] asid;
  logic [43:0] ppn;
}  rv64_satp_s;

typedef struct packed
{
  // We only support No Translation and SV39
  logic        mode;
  // We don't currently have ASID support
  // We only support 39 bit physical address.
  // TODO: Generate this based on vaddr
  logic [27:0] ppn;
}  bp_satp_s;














typedef struct packed
{
  // State Dirty
  // 0 - FS and XS are both != 11
  // 1 - set if FS or SX == 11
  //  Note: readonly
  logic        sd;
  logic [26:0] wpri1;
  // XLEN
  //   01 - 32 bit data
  //   10 - 64 bit data
  //   11 - 128 bit data
  // MXL is in misa instead.
  logic [1:0]  sxl;
  logic [1:0]  uxl;
  logic [8:0]  wpri2;
  // Trap SRET
  // 0 - SRET permitted in S-mode
  // 1 - SRET in S-mode is illegal
  logic        tsr;
  // Trap WFI
  // 0 - WFI is permitted in S-mode
  // 1 - WFI is executed and not complete within implementation-defined time, is illegal
  logic        tw;
  // Trap VM
  // 0 - The following operations are legal
  // 1 - attempts to read or write satp or execute SFENCE.VMA in S-mode are illegal
  logic        tvm;
  // Make Executable Readable
  //   0 - only loads from pages marked readable succeed
  //   1 - loads from pages marked either readable or executable succeed
  //   No effect when translation is disabled
  logic        mxr;
  // Supervisor User Memory
  //   0 - S-mode memory accesses to U-mode pages will fault
  //   1 - S-mode memory accesses to U-mode pages will succeed
  logic        sum;
  // Modify Privilege
  //   0 - translation and protection behave normally
  //   1 - load and stores are translated as though privilege mode is MPP
  logic        mprv;
  // Extension Status
  //   0 - off
  //   1 - initial (none dirty or clean)
  //   2 - clean (none dirty)
  //   3 - dirty
  // Hardwired to 0 in systems without extensions requiring context (vector)
  logic [1:0]  xs;
  // Floating-point Status
  //   0 - off
  //   1 - initial (none dirty or clean)
  //   2 - clean (none dirty)
  //   3 - dirty
  // Hardwired to 0 in systems without extensions requiring context (floating point)
  logic [1:0]  fs;
  // Previous Privilege
  //   11 - M
  //   01 - S
  //   00 - U
  logic [1:0]  mpp;
  logic [1:0]  wpri3;
  logic        spp;
  // Previous Interrupt Enable
  //   0 - Interrupt Previously Disabled for Privilege Mode
  //   1 - Interrupt Previously Enabled for Privilege Mode
  logic        mpie;
  logic        wpri4;
  logic        spie;
  logic        upie;
  // Global Interrupt Enable
  //   0 - Interrupt Disabled for Privilege Mode
  //   1 - Interrupt Enabled for Privilege Mode
  logic        mie;
  logic        wpri5;
  logic        sie;
  logic        uie; 
}  rv64_mstatus_s;

typedef struct packed
{
  logic       mprv;

  logic [1:0] mpp;
  logic       spp;

  logic       mpie;
  logic       spie;

  logic       mie;
  logic       sie;
}  bp_mstatus_s;
























typedef logic [63:0] rv64_medeleg_s;
// Hardcode exception 10, 11, 14, 16+ to zero
typedef struct packed
{
  logic [15:15] deleg_15;
  logic [13:12] deleg_13to12;
  logic [ 9: 0] deleg_9to0;
}  bp_medeleg_s;















typedef struct packed
{
  logic [51:0] wpri1;
  // M-mode External Interrupt Delegation
  logic        mei;
  logic        wpri2;
  // S-mode External Interrupt Delegation
  logic        sei;
  // U-mode External Interrupt Delegation
  logic        uei;
  // M-mode Timer Interrupt Delegation
  logic        mti;
  logic        wpri3;
  // S-mode Timer Interrupt Delegation
  logic        sti;
  // U-mode Timer Interrupt Delegation
  logic        uti;
  // M-mode Software Interrupt Delegation
  logic        msi;
  logic        wpri4;
  // S-mode Software Interrupt Delegation
  logic        ssi;
  // U-mode Software Interrupt Delegation
  logic        usi;
}  rv64_mideleg_s;

typedef struct packed
{
  logic mei;
  logic sei;
  
  logic mti;
  logic sti;

  logic msi;
  logic ssi;
}  bp_mideleg_s;
























typedef struct packed
{
  logic [51:0] wpri1;
  // M-mode External Interrupt Enable
  logic        meie;
  logic        wpri2;
  // S-mode External Interrupt Enable
  logic        seie;
  // U-mode External Interrupt Enable
  logic        ueie;
  // M-mode Timer Interrupt Enable
  logic        mtie;
  logic        wpri3;
  // S-mode Timer Interrupt Enable
  logic        stie;
  // U-mode Timer Interrupt Enable
  logic        utie;
  // M-mode Software Interrupt Enable
  logic        msie;
  logic        wpri4;
  // S-mode Software Interrupt Enable
  logic        ssie;
  // U-mode Software Interrupt Enable
  logic        usie;
}  rv64_mie_s;

typedef struct packed 
{
  logic meie;
  logic seie;

  logic mtie;
  logic stie;

  logic msie;
  logic ssie;
}  bp_mie_s;
























typedef struct packed
{
  // Base address for traps
  logic [61:0] base;
  // Trap Mode
  //   00 - Direct, all exceptions set pc to BASE
  //   01 - Vectored, interrupts set pc to BASE+4xcause
  logic [1:0]  mode;
}  rv64_mtvec_s;

typedef struct packed
{
  logic [38:0] base;
}  bp_mtvec_s;











typedef struct packed
{
  logic [31:3] hpm;
  logic        ir;
  logic        tm;
  logic        cy;
}  rv64_mcounteren_s;

typedef struct packed
{
  logic ir;
  logic cy;
}  bp_mcounteren_s;














typedef logic [63:0] rv64_mscratch_s;
typedef logic [63:0] bp_mscratch_s;







typedef struct packed
{
  logic [51:0] wpri1;
  // M-mode External Interrupt Pending
  logic        meip;
  logic        wpri2;
  // S-mode External Interrupt Pending
  logic        seip;
  // U-mode External Interrupt Pending
  logic        ueip;
  // M-mode Timer Interrupt Pending
  logic        mtip;
  logic        wpri3;
  // S-mode Timer Interrupt Pending
  logic        stip;
  // U-mode Timer Interrupt Pending
  logic        utip;
  // M-mode Software Interrupt Pending
  logic        msip;
  logic        wpri4;
  // S-mode Software Interrupt Pending
  logic        ssip;
  // U-mode Software Interrupt Pending
  logic        usip;
}  rv64_mip_s;

typedef struct packed
{
  logic meip;
  logic seip;

  logic mtip;
  logic stip;

  logic msip;
  logic ssip;
}   bp_mip_s;
























typedef logic [63:0] rv64_mtval_s;
typedef struct packed
{
  logic sgn;
  logic [39:0] addr;
}  bp_mtval_s;







typedef logic [63:0] rv64_mepc_s;
typedef struct packed
{
  logic sgn;
  logic [39:0] addr;
}  bp_mepc_s;







typedef struct packed
{
  // Locked - writes to this pmpcfg and corresponding pmpaddr are ignored
  logic          l;
  logic [1:0] wpri;
  // Address Matching Mode
  //  00 - Off  , Null region (disabled)
  //  01 - TOR  , Top of range (pmpaddr[i-1] <= a < pmpaddr[i], or 0 <= a < pmpaddr[0])
  //  10 - NA4  , Naturally aligned four-byte region 
  //  11 - NAPOT, Naturally aligned power-of-two region
  logic [1:0]    a;
  // Execute permissions
  logic          x;
  // Write permissions
  logic          w;
  // Read permissions
  logic          r;
}  rv64_pmpcfg_entry_s;

typedef struct packed
{
  rv64_pmpcfg_entry_s [7:0] pmpcfg;
}  rv64_pmpcfg_s;
typedef rv64_pmpcfg_s rv64_pmpcfg0_s;
typedef rv64_pmpcfg_s rv64_pmpcfg1_s;

typedef struct packed
{
  rv64_pmpcfg_entry_s [3:0] pmpcfg;
}  bp_pmpcfg_s;

typedef bp_pmpcfg_s bp_pmpcfg0_s;












typedef struct packed
{
  logic [9:0]  warl;
  logic [53:0] addr_55_2;
}  rv64_pmpaddr_s;

typedef rv64_pmpaddr_s rv64_pmpaddr0_s;
typedef rv64_pmpaddr_s rv64_pmpaddr1_s;
typedef rv64_pmpaddr_s rv64_pmpaddr2_s;
typedef rv64_pmpaddr_s rv64_pmpaddr3_s;

typedef struct packed
{
  logic [37:0] addr_39_2;
}  bp_pmpaddr_s;

typedef bp_pmpaddr_s bp_pmpaddr0_s;
typedef bp_pmpaddr_s bp_pmpaddr1_s;
typedef bp_pmpaddr_s bp_pmpaddr2_s;
typedef bp_pmpaddr_s bp_pmpaddr3_s;



















typedef struct packed
{
  logic        _interrupt;
  logic [62:0] ecode;
}  rv64_mcause_s;

typedef struct packed
{
  logic       _interrupt;
  logic [3:0] ecode;
}  bp_mcause_s;











typedef logic [63:0] rv64_mcounter_s;
typedef logic [47:0] bp_mcounter_s;







typedef rv64_mcounter_s rv64_mcycle_s;
typedef rv64_mcounter_s rv64_minstret_s;

typedef bp_mcounter_s bp_mcycle_s;
typedef bp_mcounter_s bp_minstret_s;







typedef struct packed
{
  logic [31:3] hpm;
  logic        ir;
  logic        warl;
  logic        cy;
}  rv64_mcountinhibit_s;

typedef struct packed
{
  logic ir;
  logic cy;
}  bp_mcountinhibit_s;




























































  localparam rv64_rf_els_gp         = 32;
  localparam rv64_instr_width_gp    = 32;
  localparam rv64_eaddr_width_gp    = 64;
  localparam rv64_byte_width_gp     = 8;
  localparam rv64_hword_width_gp    = 16;
  localparam rv64_word_width_gp     = 32;
  localparam rv64_dword_width_gp    = 64;
  localparam rv64_reg_data_width_gp = 64;
  localparam rv64_reg_addr_width_gp = 5;
  localparam rv64_shamt_width_gp    = 6;
  localparam rv64_shamtw_width_gp   = 5;
  localparam rv64_opcode_width_gp   = 7;
  localparam rv64_funct3_width_gp   = 3;
  localparam rv64_funct7_width_gp   = 7;
  localparam rv64_csr_addr_width_gp = 12;
  localparam rv64_imm20_width_gp    = 20;
  localparam rv64_imm12_width_gp    = 12;
  localparam rv64_imm11to5_width_gp = 7;
  localparam rv64_imm4to0_width_gp  = 5;
  localparam rv64_priv_width_gp     = 2;

  typedef struct packed
  {
    logic [rv64_funct7_width_gp-1:0]   funct7;
    logic [rv64_reg_addr_width_gp-1:0] rs2_addr;
    logic [rv64_reg_addr_width_gp-1:0] rs1_addr;
    logic [rv64_funct3_width_gp-1:0]   funct3;
    logic [rv64_reg_addr_width_gp-1:0] rd_addr;
  }  rv64_instr_rtype_s;

  typedef struct packed
  {
    logic [rv64_imm12_width_gp-1:0]    imm12;
    logic [rv64_reg_addr_width_gp-1:0] rs1;
    logic [rv64_funct3_width_gp-1:0]   funct3;
    logic [rv64_reg_addr_width_gp-1:0] rd_addr;
  }  rv64_instr_itype_s;

  typedef struct packed
  {
    logic [rv64_imm11to5_width_gp-1:0] imm11to5;
    logic [rv64_reg_addr_width_gp-1:0] rs2;
    logic [rv64_reg_addr_width_gp-1:0] rs1;
    logic [rv64_funct3_width_gp-1:0]   funct3;
    logic [rv64_imm4to0_width_gp-1:0]  imm4to0;
  }  rv64_instr_stype_s;

  typedef struct packed 
  {
    logic [rv64_imm20_width_gp-1:0]    imm20;
    logic [rv64_reg_addr_width_gp-1:0] rd_addr;
  }  rv64_instr_utype_s;

  typedef struct packed
  {
    union packed
    {
      rv64_instr_rtype_s rtype;
      rv64_instr_itype_s itype;
      rv64_instr_stype_s stype;
      rv64_instr_utype_s utype;
    }  fields;
    logic [rv64_opcode_width_gp-1:0]   opcode;
  }  rv64_instr_s;

endpackage

package bp_common_aviary_pkg;
  /**
 *
 * bp_common_aviary_defines.vh
 *
 */




// Thoughts: 
// Hardcoding hartid and lceid width limits us to 8 cores for our standard configurations,
//   but would allow the hierachical flow to reuse a single BP core for both dual-core and
//   oct-core configurations.
// typedef logic[2:0] bp_mhartid_t;
// typedef logic[3:0] bp_lce_id_t;
//
// We could pass pc_entry_point here as logic.  We could also pass it as a bsg_tag message

// Passing in proc_cfg as a port rather than a parameter limits some optimizations (need to 
//   route the ids through the chip), but it allows us to stamp out cores in our flow
// mhartid   - the hartid for the core. Since BP does not support SMT, hartid == coreid
// icache_id - the lceid used for coherence operations
// dcache_id - the lceid used for coherence operations 












typedef struct packed
{
  integer num_core;
  integer num_cce;
  integer num_lce;

  integer vaddr_width;
  integer paddr_width;
  integer asid_width;

  integer branch_metadata_fwd_width;
  integer btb_tag_width;
  integer btb_idx_width;
  integer bht_idx_width;
  integer ras_idx_width;

  integer itlb_els;
  integer dtlb_els;

  integer lce_sets;
  integer lce_assoc;
  integer cce_block_width;
  integer num_cce_instr_ram_els;

  integer fe_queue_fifo_els;
  integer fe_cmd_fifo_els;

  integer async_coh_clk;
  integer coh_noc_flit_width;
  integer coh_noc_cid_width;
  integer coh_noc_len_width;
  integer coh_noc_y_cord_width;
  integer coh_noc_x_cord_width;
  integer coh_noc_y_dim;
  integer coh_noc_x_dim;

  integer cfg_core_width;
  integer cfg_addr_width;
  integer cfg_data_width;

  integer async_mem_clk;
  integer mem_noc_max_credits;
  integer mem_noc_flit_width;
  integer mem_noc_reserved_width;
  integer mem_noc_cid_width;
  integer mem_noc_len_width;
  integer mem_noc_y_cord_width;
  integer mem_noc_x_cord_width;
  integer mem_noc_y_dim;
  integer mem_noc_x_dim;
}  bp_proc_param_s;














































































  // Suitably high enough to not run out of configs.
  localparam max_cfgs    = 128;
  localparam lg_max_cfgs = ( ((max_cfgs)==1) ? 1 : $clog2((max_cfgs)));

  localparam bp_proc_param_s bp_inv_cfg_p = 
    '{default: "inv"};

  localparam bp_proc_param_s bp_half_core_cfg_p = 
    '{num_core: 1
      ,num_cce: 1
      ,num_lce: 1

      ,vaddr_width: 39
      ,paddr_width: 40
      ,asid_width : 1
      
      ,branch_metadata_fwd_width: 28
      ,btb_tag_width            : 10
      ,btb_idx_width            : 6
      ,bht_idx_width            : 9
      ,ras_idx_width            : 2

      ,itlb_els             : 8
      ,dtlb_els             : 8
      
      ,lce_sets             : 64
      ,lce_assoc            : 8
      ,cce_block_width      : 512
      ,num_cce_instr_ram_els: 256

      ,fe_queue_fifo_els: 8
      ,fe_cmd_fifo_els  : 2

      ,async_coh_clk       : 0
      ,coh_noc_flit_width  : 62
      ,coh_noc_cid_width   : 2
      ,coh_noc_len_width   : 5
      ,coh_noc_y_cord_width: 0
      ,coh_noc_x_cord_width: 1
      ,coh_noc_y_dim       : 1
      ,coh_noc_x_dim       : 1

      ,cfg_core_width: 8
      ,cfg_addr_width: 16
      ,cfg_data_width: 32

      ,async_mem_clk         : 0
      ,mem_noc_max_credits   : 4
      ,mem_noc_flit_width    : 30
      ,mem_noc_reserved_width: 2
      ,mem_noc_cid_width     : 2
      ,mem_noc_len_width     : 5
      ,mem_noc_y_cord_width  : 0
      ,mem_noc_x_cord_width  : 8
      ,mem_noc_y_dim         : 1
      ,mem_noc_x_dim         : 1
      };

  localparam bp_proc_param_s bp_single_core_cfg_p = 
    '{num_core: 1
      ,num_cce: 1
      ,num_lce: 2

      ,vaddr_width: 39
      ,paddr_width: 40
      ,asid_width : 1
      
      ,branch_metadata_fwd_width: 28
      ,btb_tag_width            : 10
      ,btb_idx_width            : 6
      ,bht_idx_width            : 9
      ,ras_idx_width            : 2
      
      ,itlb_els             : 8
      ,dtlb_els             : 8
      
      ,lce_sets             : 64
      ,lce_assoc            : 8
      ,cce_block_width      : 512
      ,num_cce_instr_ram_els: 256

      ,fe_queue_fifo_els: 8
      ,fe_cmd_fifo_els  : 2

      ,async_coh_clk       : 0
      ,coh_noc_flit_width  : 62
      ,coh_noc_cid_width   : 2
      ,coh_noc_len_width   : 5
      ,coh_noc_y_cord_width: 1
      ,coh_noc_x_cord_width: 1
      ,coh_noc_y_dim       : 1
      ,coh_noc_x_dim       : 1

      ,cfg_core_width: 8
      ,cfg_addr_width: 16
      ,cfg_data_width: 32

      ,async_mem_clk         : 0
      ,mem_noc_max_credits   : 4
      ,mem_noc_flit_width    : 30
      ,mem_noc_reserved_width: 2
      ,mem_noc_cid_width     : 5
      ,mem_noc_len_width     : 5
      ,mem_noc_y_cord_width  : 1
      ,mem_noc_x_cord_width  : 8
      ,mem_noc_y_dim         : 1
      ,mem_noc_x_dim         : 1
      };

  localparam bp_proc_param_s bp_dual_core_cfg_p = 
    '{num_core: 2
      ,num_cce: 2
      ,num_lce: 4
      
      ,vaddr_width: 39
      ,paddr_width: 40
      ,asid_width : 1
      
      ,branch_metadata_fwd_width: 28
      ,btb_tag_width            : 10
      ,btb_idx_width            : 6
      ,bht_idx_width            : 9
      ,ras_idx_width            : 2
      
      ,itlb_els             : 8
      ,dtlb_els             : 8
      
      ,lce_sets             : 64
      ,lce_assoc            : 8
      ,cce_block_width      : 512
      ,num_cce_instr_ram_els: 256

      ,fe_queue_fifo_els: 8
      ,fe_cmd_fifo_els  : 2

      ,async_coh_clk       : 0
      ,coh_noc_flit_width  : 62
      ,coh_noc_cid_width   : 2
      ,coh_noc_len_width   : 5
      ,coh_noc_y_cord_width: 1
      ,coh_noc_x_cord_width: 2
      ,coh_noc_y_dim       : 1
      ,coh_noc_x_dim       : 2

      ,cfg_core_width: 8
      ,cfg_addr_width: 16
      ,cfg_data_width: 32

      ,async_mem_clk         : 0
      ,mem_noc_max_credits   : 4
      ,mem_noc_flit_width    : 30
      ,mem_noc_reserved_width: 2
      ,mem_noc_cid_width     : 2
      ,mem_noc_len_width     : 5
      ,mem_noc_y_cord_width  : 1
      ,mem_noc_x_cord_width  : 7
      ,mem_noc_y_dim         : 1
      ,mem_noc_x_dim         : 2
      };

  localparam bp_proc_param_s bp_quad_core_cfg_p = 
    '{num_core: 4
      ,num_cce: 4
      ,num_lce: 8
      
      ,vaddr_width: 39
      ,paddr_width: 40
      ,asid_width : 1
      
      ,branch_metadata_fwd_width: 28
      ,btb_tag_width            : 10
      ,btb_idx_width            : 6
      ,bht_idx_width            : 9
      ,ras_idx_width            : 2
      
      ,itlb_els             : 8
      ,dtlb_els             : 8
      
      ,lce_sets             : 64
      ,lce_assoc            : 8
      ,cce_block_width      : 512
      ,num_cce_instr_ram_els: 256

      ,fe_queue_fifo_els: 8
      ,fe_cmd_fifo_els  : 2

      ,async_coh_clk       : 0
      ,coh_noc_flit_width  : 62
      ,coh_noc_cid_width   : 2
      ,coh_noc_len_width   : 5
      ,coh_noc_y_cord_width: 1
      ,coh_noc_x_cord_width: 1
      ,coh_noc_y_dim       : 2
      ,coh_noc_x_dim       : 2

      ,cfg_core_width: 8
      ,cfg_addr_width: 16
      ,cfg_data_width: 32

      ,async_mem_clk         : 1
      ,mem_noc_max_credits   : 4
      ,mem_noc_flit_width    : 30
      ,mem_noc_reserved_width: 2
      ,mem_noc_cid_width     : 2
      ,mem_noc_len_width     : 5
      ,mem_noc_y_cord_width  : 2
      ,mem_noc_x_cord_width  : 6
      ,mem_noc_y_dim         : 2
      ,mem_noc_x_dim         : 2
      };

  localparam bp_proc_param_s bp_oct_core_cfg_p = 
    '{num_core: 8
      ,num_cce: 8
      ,num_lce: 16
      
      ,vaddr_width: 39
      ,paddr_width: 40
      ,asid_width : 1
      
      ,branch_metadata_fwd_width: 28
      ,btb_tag_width            : 10
      ,btb_idx_width            : 6
      ,bht_idx_width            : 9
      ,ras_idx_width            : 2
      
      ,itlb_els             : 8
      ,dtlb_els             : 8
      
      ,lce_sets             : 64
      ,lce_assoc            : 8
      ,cce_block_width      : 512
      ,num_cce_instr_ram_els: 256

      ,fe_queue_fifo_els: 8
      ,fe_cmd_fifo_els  : 2

      ,async_coh_clk       : 0
      ,coh_noc_flit_width  : 62
      ,coh_noc_cid_width   : 2
      ,coh_noc_len_width   : 5
      ,coh_noc_y_cord_width: 0
      ,coh_noc_x_cord_width: 4
      ,coh_noc_y_dim       : 0
      ,coh_noc_x_dim       : 4

      ,cfg_core_width: 8
      ,cfg_addr_width: 16
      ,cfg_data_width: 32

      ,async_mem_clk         : 0
      ,mem_noc_max_credits   : 4
      ,mem_noc_flit_width    : 30
      ,mem_noc_reserved_width: 2
      ,mem_noc_cid_width     : 2
      ,mem_noc_len_width     : 5
      ,mem_noc_y_cord_width  : 0
      ,mem_noc_x_cord_width  : 8
      ,mem_noc_y_dim         : 1
      ,mem_noc_x_dim         : 8
      };

  localparam bp_proc_param_s bp_sexta_core_cfg_p =
    '{num_core: 16
      ,num_cce: 16
      ,num_lce: 32

      ,vaddr_width: 39
      ,paddr_width: 40
      ,asid_width : 1

      ,branch_metadata_fwd_width: 28
      ,btb_tag_width            : 10
      ,btb_idx_width            : 6
      ,bht_idx_width            : 9
      ,ras_idx_width            : 2

      ,itlb_els             : 8
      ,dtlb_els             : 8
      
      ,lce_sets             : 64
      ,lce_assoc            : 8
      ,cce_block_width      : 512
      ,num_cce_instr_ram_els: 256

      ,fe_queue_fifo_els: 8
      ,fe_cmd_fifo_els  : 2

      ,async_coh_clk       : 0
      ,coh_noc_flit_width  : 62
      ,coh_noc_cid_width   : 2
      ,coh_noc_len_width   : 5
      ,coh_noc_y_cord_width: 0
      ,coh_noc_x_cord_width: 4
      ,coh_noc_y_dim       : 0
      ,coh_noc_x_dim       : 16

      ,cfg_core_width: 8
      ,cfg_addr_width: 16
      ,cfg_data_width: 32

      ,async_mem_clk         : 0
      ,mem_noc_max_credits   : 4
      ,mem_noc_flit_width    : 30
      ,mem_noc_reserved_width: 2
      ,mem_noc_cid_width     : 2
      ,mem_noc_len_width     : 5
      ,mem_noc_y_cord_width  : 0
      ,mem_noc_x_cord_width  : 9
      ,mem_noc_y_dim         : 4
      ,mem_noc_x_dim         : 4
      };

  typedef enum bit [lg_max_cfgs-1:0] 
  {
    e_bp_sexta_core_cfg     = 6
    ,e_bp_oct_core_cfg      = 5
    ,e_bp_quad_core_cfg     = 4
    ,e_bp_dual_core_cfg     = 3
    ,e_bp_single_core_cfg   = 2
    ,e_bp_half_core_cfg     = 1
    ,e_bp_inv_cfg           = 0
  } bp_cfg_e;

  /* verilator lint_off WIDTH */     
  parameter bp_proc_param_s [max_cfgs-1:0] all_cfgs_gp =
  {
    bp_sexta_core_cfg_p
    ,bp_oct_core_cfg_p
    ,bp_quad_core_cfg_p
    ,bp_dual_core_cfg_p
    ,bp_single_core_cfg_p
    ,bp_half_core_cfg_p
    ,bp_inv_cfg_p
  };
  /* verilator lint_on WIDTH */

endpackage

package bp_be_pkg;
  import bp_common_pkg::*;
  import bp_common_rv64_pkg::*;

  /**
 *
 * bp_common_fe_be_if.vh
 *
 * bp_fe_be_interface.vh declares the interface between the BlackParrot Front End
 * and Back End For simplicity and flexibility, these signals are declared as
 * parameterizable structures. Each structure declares its width separately to
 * avoid preprocessor ordering issues.
 *
 * Logically, the BE controls the FE and may command the FE to flush all the states,
 * redirect the PC, etc. The FE uses its queue to supply the BE with (possibly
 * speculative) instruction/PC pairs and inform the BE of any exceptions that have
 * occurred within the unit (e.g., misaligned instruction fetch) so the BE may
 * ensure all exceptions are taken precisely.  The BE checks the PC in the
 * instruction/PC pairs to make sure that the FE predictions correspond to
 * correct architectural execution.
 *
 * NOTE: VCS can only handle packed unions where each member is the same size. Therefore, we
 *         need to do some macro hacking to get parameterized unions to work nicely.
 * NOTE: Potentially could make sense to separate two unidirectional interface files. This one
 *         is a little overwhelming.
 */





































































































































































































































































































































































































  


/* int_fu_op [2:0] is equivalent to funct3 in the RV instruction.
 * int_fu_op [3] is an alternate version of that operation.
 */
typedef enum bit [3:0]
{
  e_int_op_add        = 4'b0000
  ,e_int_op_sub       = 4'b1000
  ,e_int_op_sll       = 4'b0001
  ,e_int_op_slt       = 4'b0010
  ,e_int_op_sge       = 4'b1010
  ,e_int_op_sltu      = 4'b0011
  ,e_int_op_sgeu      = 4'b1011
  ,e_int_op_xor       = 4'b0100
  ,e_int_op_eq        = 4'b1100
  ,e_int_op_srl       = 4'b0101
  ,e_int_op_sra       = 4'b1101
  ,e_int_op_or        = 4'b0110
  ,e_int_op_ne        = 4'b1110
  ,e_int_op_and       = 4'b0111
  ,e_int_op_pass_src2 = 4'b1111
} bp_be_int_fu_op_e;

typedef enum bit [3:0]
{
  e_lb     = 4'b0000
  ,e_lh    = 4'b0001
  ,e_lw    = 4'b0010
  ,e_ld    = 4'b0011
  ,e_lbu   = 4'b0100
  ,e_lhu   = 4'b0101
  ,e_lwu   = 4'b0110

  ,e_sb    = 4'b1000
  ,e_sh    = 4'b1001
  ,e_sw    = 4'b1010
  ,e_sd    = 4'b1011

  ,e_lrw   = 4'b0111
  ,e_scw   = 4'b1100

  ,e_lrd   = 4'b1101
  ,e_scd   = 4'b1110

  ,e_itlb_fill = 4'b1111
} bp_be_mmu_fu_op_e;

typedef enum bit [3:0]
{
  e_csrrw   = 4'b0001
  ,e_csrrs  = 4'b0010
  ,e_csrrc  = 4'b0011
  ,e_csrrwi = 4'b0101
  ,e_csrrsi = 4'b0110
  ,e_csrrci = 4'b0111

  ,e_mret   = 4'b1011
  ,e_sret   = 4'b1001

  // TODO: Think more carefully about these encodings
  ,e_ecall      = 4'b1110
  ,e_wfi        = 4'b1100
  ,e_ebreak     = 4'b1111

  ,e_sfence_vma = 4'b1101

  // We treat FE exceptions as CSR ops
  ,e_op_illegal_instr      = 4'b0000
  ,e_op_instr_access_fault = 4'b0100
  ,e_op_instr_misaligned   = 4'b1010
} bp_be_csr_fu_op_e;

typedef struct packed
{
  union packed
  {
    bp_be_int_fu_op_e int_fu_op;
    bp_be_mmu_fu_op_e mmu_fu_op;
    bp_be_csr_fu_op_e csr_fu_op;
  }  fu_op;
}  bp_be_fu_op_s;

typedef enum bit
{
  e_src1_is_rs1 = 1'b0
  ,e_src1_is_pc = 1'b1
} bp_be_src1_e;

typedef enum bit
{
  e_src2_is_rs2  = 1'b0
  ,e_src2_is_imm = 1'b1
} bp_be_src2_e;

typedef enum bit
{
  e_baddr_is_pc   = 1'b0
  ,e_baddr_is_rs1 = 1'b1
} bp_be_baddr_e;

typedef enum bit
{
  e_offset_is_imm   = 1'b0
  ,e_offset_is_zero = 1'b1
} bp_be_offset_e;

typedef enum bit
{
  e_result_from_alu       = 1'b0
  ,e_result_from_pc_plus4 = 1'b1
} bp_be_result_e;

typedef struct packed
{
  logic                             v;
  logic                             instr_v;

  logic                             pipe_comp_v;
  logic                             pipe_int_v;
  logic                             pipe_mul_v;
  logic                             pipe_mem_v;
  logic                             pipe_fp_v;

  logic                             irf_w_v;
  logic                             frf_w_v;
  logic                             mem_v;
  logic                             dcache_r_v;
  logic                             dcache_w_v;
  logic                             csr_v;
  logic                             fencei_v;
  logic                             fp_not_int_v;
  logic                             jmp_v;
  logic                             br_v;
  logic                             opw_v;

  bp_be_fu_op_s                     fu_op;

  bp_be_src1_e                      src1_sel;
  bp_be_src2_e                      src2_sel;
  bp_be_baddr_e                     baddr_sel;
  bp_be_offset_e                    offset_sel;
  bp_be_result_e                    result_sel;
}  bp_be_decode_s;

typedef struct packed
{
  // RISC-V exceptions
  logic store_page_fault;
  logic reserved2;
  logic load_page_fault;
  logic instr_page_fault;
  logic ecall_m_mode;
  logic reserved1;
  logic ecall_s_mode;
  logic ecall_u_mode;
  logic store_fault;
  logic store_misaligned;
  logic load_fault;
  logic load_misaligned;
  logic breakpoint;
  logic illegal_instr;
  logic instr_fault;
  logic instr_misaligned;
}  bp_be_ecode_dec_s;




typedef struct packed
{
  // BE exceptional conditions
  logic fe_nop_v;
  logic be_nop_v;
  logic me_nop_v;
  logic poison_v;
  logic roll_v;
}  bp_be_exception_s;













  































  typedef struct packed 
  {
    logic [bp_sv39_pte_width_gp-10-bp_sv39_ppn_width_gp-1:0] reserved;
    logic [bp_sv39_ppn_width_gp-1:0] ppn;
    logic [1:0] rsw;
    logic d;
    logic a;
    logic g;
    logic u;
    logic x;
    logic w;
    logic r;
    logic v;
  }  bp_sv39_pte_s;













  /**
 *
 * bp_be_internal_if_defines.vh
 *
 */




/*
 * Clients need only use this macro to declare all parameterized structs for FE<->BE interface.
 */









































































































/* Declare width macros so that clients can use structs in ports before struct declaration
 * Each of these macros needs to be kept in sync with the struct definition. The computation
 *   comes from literally counting bits in the struct definition, which is ugly, error-prone,
 *   and an unfortunate, necessary consequence of parameterized structs.
 */













































endpackage : bp_be_pkg

package bp_be_dcache_pkg;
    
  
  /**
 *  Name:
 *    bp_be_dcache_pkt.vh
 *
 *  Description:
 *    dcache packet format to be sent from mmu.
 */
















  /**
 *  Name:
 *    bp_be_dcache_lce_pkt.vh
 *
 *  Description:
 *    packet definition that LCE uses to access data_mem, tag_mem, and stat_mem.
 */




/**
 * bp_common_me_if.vh
 *
 * This file defines the interface between the CCEs and LCEs, and the CCEs and memory in the
 * BlackParrot coherence system. For ease of reuse and flexiblity, this interface is defined as a
 * collection of parameterized structs.
 *
 */



























































































































































































































































































































































































//  data_mem pkt
//












//  tag_mem pkt
//













//  stat_mem pkt
//













  /**
 *  Name:
 *    bp_be_dcache_tag_info.vh
 *
 *  Description:
 *    dcache tag_mem format.
 */




/**
 * bp_common_me_if.vh
 *
 * This file defines the interface between the CCEs and LCEs, and the CCEs and memory in the
 * BlackParrot coherence system. For ease of reuse and flexiblity, this interface is defined as a
 * collection of parameterized structs.
 *
 */






































































































































































































































































































































































































  /**
 *  Name:
 *    bp_be_dcache_stat_info.vh
 *
 *  Description:
 *    stat_mem entry format.
 */















  /**
 *  Name:
 *    bp_be_dcache_wbuf_entry.vh
 *
 *  Description:
 *    dcache write buffer entry format.
 */



















  typedef enum logic [3:0] {

    e_dcache_opcode_lbu  = 4'b0100 // load byte unsigned
    ,e_dcache_opcode_lhu = 4'b0101 // load half unsigned
    ,e_dcache_opcode_lwu = 4'b0110 // load word unsigned

    ,e_dcache_opcode_lb  = 4'b0000 // load byte
    ,e_dcache_opcode_lh  = 4'b0001 // load half
    ,e_dcache_opcode_lw  = 4'b0010 // load word
    ,e_dcache_opcode_ld  = 4'b0011 // load double

    ,e_dcache_opcode_sb  = 4'b1000 // store byte
    ,e_dcache_opcode_sh  = 4'b1001 // store half
    ,e_dcache_opcode_sw  = 4'b1010 // store word
    ,e_dcache_opcode_sd  = 4'b1011 // store double

    ,e_dcache_opcode_lrw = 4'b0111 // load reserved word
    ,e_dcache_opcode_scw = 4'b1100 // store conditional word

    ,e_dcache_opcode_lrd = 4'b1101 // load reserved double
    ,e_dcache_opcode_scd = 4'b1110 // store conditional double
  } bp_be_dcache_opcode_e;


  // LCE data_mem_pkt opcode
  //
  typedef enum logic [1:0] {
   
    // write cache block 
    e_dcache_lce_data_mem_write,

    // read cache block
    e_dcache_lce_data_mem_read,

    // write uncached load data
    e_dcache_lce_data_mem_uncached
    
  } bp_be_dcache_lce_data_mem_opcode_e;

  //  LCE tag_mem_pkt opcode
  //
  typedef enum logic [1:0] {

    // clear all blocks in a set for given index.
    e_dcache_lce_tag_mem_set_clear,
    
    // invalidate a block for given index and way_id.
    e_dcache_lce_tag_mem_invalidate,
    
    // set tag and coh_state for given index and way_id.
    e_dcache_lce_tag_mem_set_tag

  } bp_be_dcache_lce_tag_mem_opcode_e;


  // LCE stat_mem_pkt opcode
  //
  typedef enum logic [1:0] {

    // clear all dirty bits and LRU bits to zero for given index.
    e_dcache_lce_stat_mem_set_clear,
    
    // read stat_info for given index.
    e_dcache_lce_stat_mem_read,
    
    // clear dirty bit for given index and way_id.
    e_dcache_lce_stat_mem_clear_dirty

  } bp_be_dcache_lce_stat_mem_opcode_e;

  // LCE Mode
  typedef enum logic {
    e_dcache_lce_mode_uncached
    ,e_dcache_lce_mode_normal
  } bp_be_dcache_lce_mode_e;

  

endpackage




package bp_me_nonsynth_pkg;

  // bits: 3 = store/load
  //       2 = unsigned/signed
  //     1:0 = size (1, 2, 4, 8 bytes)
  typedef enum logic [3:0] {

    e_lce_opcode_lbu  = 4'b0100 // load byte unsigned
    ,e_lce_opcode_lhu = 4'b0101 // load half unsigned
    ,e_lce_opcode_lwu = 4'b0110 // load word unsigned

    ,e_lce_opcode_lb  = 4'b0000 // load byte
    ,e_lce_opcode_lh  = 4'b0001 // load half
    ,e_lce_opcode_lw  = 4'b0010 // load word
    ,e_lce_opcode_ld  = 4'b0011 // load double

    ,e_lce_opcode_sb  = 4'b1000 // store byte
    ,e_lce_opcode_sh  = 4'b1001 // store half
    ,e_lce_opcode_sw  = 4'b1010 // store word
    ,e_lce_opcode_sd  = 4'b1011 // store double

    // TODO: LR/SC not yet supported in nonsynth mock LCE
    //,e_lce_opcode_lrw = 4'b0111  // load reserved word
    //,e_lce_opcode_scw = 4'b1100  // store conditional word

    //,e_lce_opcode_lrd = 4'b1101  // load reserved double
    //,e_lce_opcode_scd = 4'b1110  // store conditional double

  } bp_me_nonsynth_lce_opcode_e;

endpackage

/*
 * bp_me_pkg.svh
 *
 * Contains the interface structures used for communicating between the CCE and Memory.
 *
 */

package bp_me_pkg;

  import bp_common_pkg::*;

  /**
 *
 * Name:
 *   bp_mem_wormhole.svh
 *
 */





 

// aka ready & valid


// aka ready->valid


// aka valid->ready




























/******************* bsg wormhole packet definition ******************/













/******************* bsg wormhole header flit definition ******************/



























 
// this is a partial packet header should always go at the bottom bits of a header flit
// move to bsg_wormhole_router.vh
// FIXME:  have them pass in the cord_markers_pos_p
//         struct, then it will match bsg_wormhole_router
//














































































































































  /**
 *
 * Name:
 *   bp_cce_inst.svh
 *
 * Description:
 *   This file describes the CCE microcode instructions. Any changes made to this file must be
 *   reflected in the source code of the CCE microcode assembler, too.
 *
 *   This file defines both the assembler generated and internally decoded formats of the microcode.
 *
 *   Some software operations are supported via assembler transforms rather than being supported
 *   directly in hardware (e.g., ALU increment and decrement).
 *
 *   Note: this file may rely on defines from bsg_defines.h in the BaseJump STL repo.
 *   Note: this file relies on bp_common_bedrock_if.svh
 */




/*
 * Instruction width definitions
 */

// Instructions are 32-bits wide with 2 bits of attached metadata
// cce_instr_width_p should be equal to 34, and used when passing instruction+metadata





// Microcode RAM address width
// 9 bits allows up to 512 instructions
// this must be greater or equal to cce_pc_width_p in bp_common_aviary_pkg


// Immediate field widths






/*
 * General Purpose Registers
 *
 * Note: number of GPRs must be less than or equal to the number that can be
 * represented in the GPR operand enum. Currently, the maximum is 16 GPRs, but only
 * 8 are actually implemented and used.
 */


// Note: this is hard-coded so it can be used in part-select / bit-slicing expressions

//`BSG_SAFE_CLOG2(`bp_cce_inst_num_gpr)


/*
 * Major Op Codes
 */

typedef enum logic [2:0] {
  e_op_alu                               = 3'b000 // ALU operation
  ,e_op_branch                           = 3'b001 // Branch (control flow) operation
  ,e_op_reg_data                         = 3'b010 // Register data movement operation
//,e_op_mem                              = 3'b011    // Memory data operation (not implemented)
  ,e_op_flag                             = 3'b100
  ,e_op_dir                              = 3'b101
  ,e_op_queue                            = 3'b110
//,e_op_unused                           = 3'b111
} bp_cce_inst_op_e;

/*
 * Minor Op Codes
 */

// Minor ALU Op Codes
typedef enum logic [3:0] {
  e_add_op                               = 4'b0000 // Add
  ,e_sub_op                              = 4'b0001 // Subtract
  ,e_lsh_op                              = 4'b0010 // Left Shift
  ,e_rsh_op                              = 4'b0011 // Right Shift
  ,e_and_op                              = 4'b0100 // Bit-wise AND
  ,e_or_op                               = 4'b0101 // Bit-wise OR
  ,e_xor_op                              = 4'b0110 // Bit-wise XOR
  ,e_neg_op                              = 4'b0111 // Bit-wise negation (unary)
  ,e_addi_op                             = 4'b1000 // Add immediate
//,e_nop_op                              = 4'b1000   // Null Operation (r0 = r0 + 0)
//,e_inc_op                              = 4'b1000   // Increment register by 1
  ,e_subi_op                             = 4'b1001 // Subtract immediate
//,e_dec_op                              = 4'b1001   // Decrement register by 1
  ,e_lshi_op                             = 4'b1010 // Left Shift immediate
  ,e_rshi_op                             = 4'b1011 // Right Shift immediate
  ,e_not_op                              = 4'b1111 // Logical Not
} bp_cce_inst_minor_alu_op_e;

// Minor Branch Op Codes
typedef enum logic [3:0] {
  e_beq_op                               = 4'b0000 // Branch if A == B
//,e_bi_op                               = 4'b0000   // Unconditional Branch, or Branch if A == A
  ,e_bne_op                              = 4'b0001 // Branch if A != B
  ,e_blt_op                              = 4'b0010 // Branch if A < B
//,e_bgt_op                              = 4'b0010   // Branch if A > B, or B < A
  ,e_ble_op                              = 4'b0011 // Branch if A <= B
//,e_bge_op                              = 4'b0011   // Branch if A >= B, or B <= A

  ,e_bs_op                               = 4'b0100 // Branch if special == GPR
  ,e_bss_op                              = 4'b0101 // Branch if special == special

  ,e_beqi_op                             = 4'b1000 // Branch if A == immediate
//,e_bz_op                               = 4'b1000   // Branch if A == 0
  ,e_bneqi_op                            = 4'b1001 // Branch if A != immediate
//,e_bnz_op                              = 4'b1001   // Branch if A != 0

  ,e_bsi_op                              = 4'b1100 // Branch if special == immediate
} bp_cce_inst_minor_branch_op_e;

// Minor Register Data Movement Op Codes
typedef enum logic [3:0] {
  e_mov_op                               = 4'b0000 // Move GPR to GPR
  ,e_movsg_op                            = 4'b0001 // Move Special Register to GPR
  ,e_movgs_op                            = 4'b0010 // Move GPR to Special Register
  //,e_ld_flags_op                       = 4'b0010   // MSHR.flags = GPR[0+:num_flags]
  ,e_movfg_op                            = 4'b0011 // Move Flag to GPR[0]
  ,e_movgf_op                            = 4'b0100 // Move GPR[0] to Flag
  ,e_movpg_op                            = 4'b0101 // Move Param to GPR
  ,e_movgp_op                            = 4'b0110 // Move GPR to Param
  ,e_movi_op                             = 4'b1000 // Move Immediate to GPR
  ,e_movis_op                            = 4'b1001 // Move Immediate to Special Register
//,e_ld_flags_i_op                       = 4'b1001   // MSHR.flags = imm[0+:num_flags]
//,e_clf_op                              = 4'b1001   // MSHR.flags = 0
  ,e_movip_op                            = 4'b1010 // Move Immediate to Param Register
  ,e_clm_op                              = 4'b1111 // Clear MSHR register
} bp_cce_inst_minor_reg_data_op_e;

// Minor Memory Op Codes
// Note: these are not implemented in the CCE by default. In software, the e_m* operations
// operate on global memory (i.e., physical/main memory in the system). There is a bit
// in the instruction encoding to indicate local (i.e., CCE scratchpad) or global memory
// operation.
typedef enum logic [3:0] {
  e_ldb_op                               = 4'b0000 // Load byte from memory
  ,e_ldh_op                              = 4'b0001 // Load half-word from memory
  ,e_ldw_op                              = 4'b0010 // Load word from memory
  ,e_ldd_op                              = 4'b0011 // Load double-word from memory
  ,e_stb_op                              = 4'b0100 // Store byte to memory
  ,e_sth_op                              = 4'b0101 // Store half-word to memory
  ,e_stw_op                              = 4'b0110 // Store word to memory
  ,e_std_op                              = 4'b0111 // Store double-word to memory
} bp_cce_inst_minor_mem_op_e;

// Minor Flag Op Codes
typedef enum logic [3:0] {
  e_sf_op                                = 4'b0000 // Move imm[0] = 1 to flag
//,e_sfz_op                              = 4'b0000   // Move imm[0] = 0 to flag
  ,e_andf_op                             = 4'b0001 // Logical AND two flags to GPR
  ,e_orf_op                              = 4'b0010 // Logical OR two flags to GPR
  ,e_nandf_op                            = 4'b0011 // Logical NAND two flags to GPR
  ,e_norf_op                             = 4'b0100 // Logical NOR two flags to GPR
  ,e_notf_op                             = 4'b0101 // Logical not of flag

  ,e_bf_op                               = 4'b1000 // Branch if (MSHR.Flags & mask) == mask
  ,e_bfz_op                              = 4'b1001 // Branch if (MSHR.Flags & mask) == 0
  ,e_bfnz_op                             = 4'b1010 // Branch if (MSHR.Flags & mask) != 0
  ,e_bfnot_op                            = 4'b1011 // Branch if (MSHR.Flags & mask) != mask
} bp_cce_inst_minor_flag_op_e;

// Minor Directory Op Codes
typedef enum logic [3:0] {
  e_rdp_op                               = 4'b0000 // Read Pending Bit
  ,e_rdw_op                              = 4'b0001 // Read Directory Way Group
  ,e_rde_op                              = 4'b0010 // Read Directory Entry
  ,e_wdp_op                              = 4'b0100 // Write Pending Bit
  ,e_clp_op                              = 4'b0101 // Clear Pending Bit
  ,e_clr_op                              = 4'b0110 // Clear Directory Row
  ,e_wde_op                              = 4'b0111 // Write Directory Entry
  ,e_wds_op                              = 4'b1000 // Write Directory Entry State
  ,e_gad_op                              = 4'b1001 // Generate Auxiliary Data
} bp_cce_inst_minor_dir_op_e;

// Minor Queue Op Codes
// 1. poph does not dequeue data or memory, but captures the standard header fields into the MSHR,
//    and also captures the message type into the specified GPR.
// 2. popd dequeues a single 64-bit data packet into a single GPR. The user must first have at
//    at least done a poph to determine that data was available and so ucode can use size
//    field in MSHR to determine how many packets to dequeue.
// 3. popq dequeues only the header. We assume that all data has been popped off
//    either by popd commands, or by the message unit auto-forward mechanism, or by issuing
//    a pushq command that consumes the data (e.g., an explicit pushq memCmd that consumes an
//    lceResp containing writeback data). No state is written from the message to the CCE.

typedef enum logic [3:0] {
  e_wfq_op                               = 4'b0000 // Wait for Queue Valid
  ,e_pushq_op                            = 4'b0001 // Push Queue
//,e_pushqc_op                           = 4'b0001   // Push Queue Custom Message
  ,e_popq_op                             = 4'b0010 // Pop Queue - dequeue the header
  ,e_poph_op                             = 4'b0011 // Pop Header From Queue - does not pop message
  // TODO: popd not yet fully supported - will be supported after serdes changes
  ,e_popd_op                             = 4'b0100 // Pop Data From Queue
  ,e_specq_op                            = 4'b0101 // Write or read speculative access bits
  ,e_inv_op                              = 4'b1000 // Send all Invalidations based on sharers vector
} bp_cce_inst_minor_queue_op_e;

// Minor Op Code Union
typedef union packed {
  bp_cce_inst_minor_alu_op_e             alu_minor_op;
  bp_cce_inst_minor_branch_op_e          branch_minor_op;
  bp_cce_inst_minor_reg_data_op_e        reg_data_minor_op;
//bp_cce_inst_minor_mem_op_e             mem_minor_op;
  bp_cce_inst_minor_flag_op_e            flag_minor_op;
  bp_cce_inst_minor_dir_op_e             dir_minor_op;
  bp_cce_inst_minor_queue_op_e           queue_minor_op;
  //                                     unused op
} bp_cce_inst_minor_op_u;


/*
 * ALU Unit Operation
 */
typedef enum logic [3:0] {
  e_alu_add                              = 4'b0000 // Add
  ,e_alu_sub                             = 4'b0001 // Subtract
  ,e_alu_lsh                             = 4'b0010 // Left Shift
  ,e_alu_rsh                             = 4'b0011 // Right Shift
  ,e_alu_and                             = 4'b0100 // Bit-wise AND
  ,e_alu_or                              = 4'b0101 // Bit-wise OR
  ,e_alu_xor                             = 4'b0110 // Bit-wise XOR
  ,e_alu_neg                             = 4'b0111 // Bit-wise negation (unary)
  ,e_alu_not                             = 4'b1000 // Logical Not (unary)
  ,e_alu_nand                            = 4'b1001 // Logical Not of Bit-wise And
  ,e_alu_nor                             = 4'b1010 // Logical Not of Bit-wise Or
} bp_cce_inst_alu_op_e;



/*
 * Branch Unit Operation
 */
typedef enum logic [1:0] {
  e_branch_eq                            = 2'b00 // Branch if A == B
  ,e_branch_neq                          = 2'b01 // Branch if A != B
  ,e_branch_lt                           = 2'b10 // Branch if A < B
  ,e_branch_le                           = 2'b11 // Branch if A <= B
} bp_cce_inst_branch_op_e;



/*
 * Speculative Bits Unit Operation
 */
typedef enum logic [3:0] {
  e_spec_set                             = 4'b0000 // Set spec bit to 1
  ,e_spec_unset                          = 4'b0001 // Set spec bit to 0
  ,e_spec_squash                         = 4'b0010 // Set squash bit to 1, clear spec bit
  ,e_spec_fwd_mod                        = 4'b0011 // Set fwd_mod bit to 1, clear spec bit, set state to state
  ,e_spec_rd_spec                        = 4'b1000 // Read spec bit to sf
} bp_cce_inst_spec_op_e;



// Struct that defines speculative memory access tracking metadata
// This is used in the decoded instruction and the bp_cce_spec module
typedef struct packed
{
  logic                          spec;
  logic                          squash;
  logic                          fwd_mod;
  bp_coh_states_e                state;
} bp_cce_spec_s;


/*
 * Operand Selects
 */



// GPR Operand Select
// GPR's can be source or destination
typedef enum logic [3:0] {
  e_opd_r0                               = 4'b0000
  ,e_opd_r1                              = 4'b0001
  ,e_opd_r2                              = 4'b0010
  ,e_opd_r3                              = 4'b0011
  ,e_opd_r4                              = 4'b0100
  ,e_opd_r5                              = 4'b0101
  ,e_opd_r6                              = 4'b0110
  ,e_opd_r7                              = 4'b0111
} bp_cce_inst_opd_gpr_e;

// Flag Operand Select
// Flags can be source or destination
typedef enum logic [3:0] {
  e_opd_rqf                              = 4'b0000
  ,e_opd_ucf                             = 4'b0001
  ,e_opd_nerf                            = 4'b0010
  ,e_opd_nwbf                            = 4'b0011
  ,e_opd_pf                              = 4'b0100
  ,e_opd_sf                              = 4'b0101 // also not used, when would it be?
  // Basic flags from GAD
  // cached dirty == cmf | cof
  // cached maybe dirty == cmf | cof | cef
  // cached owned (transfer) == cef | cmf | cof | cff
  // cached == csf | cef | cmf | cof | cff
  // not cached == not(any c*f flag)
  // invalidate = rqf & csf
  ,e_opd_csf                             = 4'b0110
  ,e_opd_cef                             = 4'b0111
  ,e_opd_cmf                             = 4'b1000
  ,e_opd_cof                             = 4'b1001
  ,e_opd_cff                             = 4'b1010
  // special flags from GAD
  ,e_opd_rf                              = 4'b1011 // requesting LCE needs replacement
  ,e_opd_uf                              = 4'b1100 // rqf & (rsf | rof | rff)
  // atomics
  ,e_opd_arf                             = 4'b1101 // atomic request
  ,e_opd_anrf                            = 4'b1110 // atomic no return
  // coherence PMA
  ,e_opd_rcf                             = 4'b1111 // request to coherent memory
} bp_cce_inst_opd_flag_e;

// Control Flag one hot encoding
typedef enum logic [15:0] {
  e_flag_rqf                    = 16'b0000_0000_0000_0001 // request type flag
  ,e_flag_ucf                   = 16'b0000_0000_0000_0010 // uncached request flag
  ,e_flag_nerf                  = 16'b0000_0000_0000_0100 // non-exclusive request flag
  ,e_flag_nwbf                  = 16'b0000_0000_0000_1000 // null writeback flag
  ,e_flag_pf                    = 16'b0000_0000_0001_0000 // pending flag
  ,e_flag_sf                    = 16'b0000_0000_0010_0000 // speculative flag
  ,e_flag_csf                   = 16'b0000_0000_0100_0000 // cached S by other flag
  ,e_flag_cef                   = 16'b0000_0000_1000_0000 // cached E by other flag
  ,e_flag_cmf                   = 16'b0000_0001_0000_0000 // cached M by other flag
  ,e_flag_cof                   = 16'b0000_0010_0000_0000 // cached O by other flag
  ,e_flag_cff                   = 16'b0000_0100_0000_0000 // cached F by other flag
  ,e_flag_rf                    = 16'b0000_1000_0000_0000 // replacement flag
  ,e_flag_uf                    = 16'b0001_0000_0000_0000 // upgrade flag
  ,e_flag_arf                   = 16'b0010_0000_0000_0000 // atomic request flag
  ,e_flag_anrf                  = 16'b0100_0000_0000_0000 // atomic no return flag
  ,e_flag_rcf                   = 16'b1000_0000_0000_0000 // request to coherent memory flag
} bp_cce_inst_flag_onehot_e;



// Special Operand Select
typedef enum logic [3:0] {
  // MSHR fields can be source or destination
  e_opd_req_lce                          = 4'b0000 // MSHR.lce_id
  ,e_opd_req_addr                        = 4'b0001 // MSHR.paddr
  ,e_opd_req_way                         = 4'b0010 // MSHR.way_id
  ,e_opd_lru_addr                        = 4'b0011 // MSHR.lru_paddr
  ,e_opd_lru_way                         = 4'b0100 // MSHR.lru_way_id
  ,e_opd_owner_lce                       = 4'b0101 // MSHR.owner_lce_id
  ,e_opd_owner_way                       = 4'b0110 // MSHR.owner_way_id
  ,e_opd_next_coh_state                  = 4'b0111 // MSHR.next_coh_state
  ,e_opd_flags                           = 4'b1000 // MSHR.flags & imm[0+:num_flags]
  ,e_opd_msg_size                        = 4'b1001 // MSHR.msg_size
  ,e_opd_lru_coh_state                   = 4'b1010 // MSHR.lru_coh_state
  ,e_opd_owner_coh_state                 = 4'b1011 // MSHR.owner_coh_state

  // sharers vectors require src_b to provide GPR rX containing index to use
  // These can only be used as source a, not as source b or destinations
  ,e_opd_sharers_hit                     = 4'b1101 // sharers_hits[rX]
  ,e_opd_sharers_way                     = 4'b1110 // sharers_ways[rX]
  ,e_opd_sharers_state                   = 4'b1111 // sharers_states[rX]
} bp_cce_inst_opd_special_e;



// Params Operand Select
typedef enum logic [3:0] {
  // These four parameters can only be sources
  e_opd_cce_id                           = 4'b0000 // ID of this CCE
  ,e_opd_num_lce                         = 4'b0001 // total number of LCE in system
  ,e_opd_num_cce                         = 4'b0010 // total number of CCE in system
  ,e_opd_num_wg                          = 4'b0011 // Number of WG managed by this CCE
  // The following can be source or destination
  ,e_opd_auto_fwd_msg                    = 4'b0100 // Message auto-forward control
  ,e_opd_coh_state_default               = 4'b0101 // Default for MSHR.next_coh_state
} bp_cce_inst_opd_params_e;



// Queue valid signals and message types
// These can only be used as sources
typedef enum logic [3:0] {
  e_opd_mem_resp_v                       = 4'b0000
  ,e_opd_lce_resp_v                      = 4'b0001
  ,e_opd_pending_v                       = 4'b0010
  ,e_opd_lce_req_v                       = 4'b0011
  ,e_opd_lce_resp_type                   = 4'b0100
  ,e_opd_mem_resp_type                   = 4'b0101
  ,e_opd_lce_resp_data                   = 4'b0110
  ,e_opd_mem_resp_data                   = 4'b0111
  ,e_opd_lce_req_data                    = 4'b1000
} bp_cce_inst_opd_queue_e;



/*
 * Source Operands
 */

// Source Union
typedef union packed {
  bp_cce_inst_opd_gpr_e        gpr;
  bp_cce_inst_opd_flag_e       flag;
  bp_cce_inst_opd_special_e    special;
  bp_cce_inst_opd_params_e     param;
  bp_cce_inst_opd_queue_e      q;
} bp_cce_inst_src_u;

typedef enum logic [2:0] {
  e_src_sel_gpr
  ,e_src_sel_flag
  ,e_src_sel_special
  ,e_src_sel_param
  ,e_src_sel_queue
  ,e_src_sel_imm
  ,e_src_sel_zero
} bp_cce_inst_src_sel_e;



/*
 * Destination Operands
 */

// Destination Union
typedef union packed {
  bp_cce_inst_opd_gpr_e        gpr;
  bp_cce_inst_opd_flag_e       flag;
  bp_cce_inst_opd_special_e    special;
  bp_cce_inst_opd_params_e     param;
} bp_cce_inst_dst_u;

typedef enum logic [1:0] {
  e_dst_sel_gpr
  ,e_dst_sel_flag
  ,e_dst_sel_special
  ,e_dst_sel_param
} bp_cce_inst_dst_sel_e;




/*
 * MUX Controls
 *
 * These are used to pick where an address, LCE ID, or way ID are sourced from for
 * various instructions, including message and directory operations.
 */

// Address
typedef enum logic [3:0] {
  e_mux_sel_addr_r0                      = 4'b0000
  ,e_mux_sel_addr_r1                     = 4'b0001
  ,e_mux_sel_addr_r2                     = 4'b0010
  ,e_mux_sel_addr_r3                     = 4'b0011
  ,e_mux_sel_addr_r4                     = 4'b0100
  ,e_mux_sel_addr_r5                     = 4'b0101
  ,e_mux_sel_addr_r6                     = 4'b0110
  ,e_mux_sel_addr_r7                     = 4'b0111
  ,e_mux_sel_addr_mshr_req               = 4'b1000
  ,e_mux_sel_addr_mshr_lru               = 4'b1001
  ,e_mux_sel_addr_lce_req                = 4'b1010
  ,e_mux_sel_addr_lce_resp               = 4'b1011
  ,e_mux_sel_addr_mem_resp               = 4'b1100
  ,e_mux_sel_addr_pending                = 4'b1101
  ,e_mux_sel_addr_0                      = 4'b1111 // constant 0
} bp_cce_inst_mux_sel_addr_e;



// LCE ID
typedef enum logic [3:0] {
  e_mux_sel_lce_r0                       = 4'b0000
  ,e_mux_sel_lce_r1                      = 4'b0001
  ,e_mux_sel_lce_r2                      = 4'b0010
  ,e_mux_sel_lce_r3                      = 4'b0011
  ,e_mux_sel_lce_r4                      = 4'b0100
  ,e_mux_sel_lce_r5                      = 4'b0101
  ,e_mux_sel_lce_r6                      = 4'b0110
  ,e_mux_sel_lce_r7                      = 4'b0111
  ,e_mux_sel_lce_mshr_req                = 4'b1000
  ,e_mux_sel_lce_mshr_owner              = 4'b1001
  ,e_mux_sel_lce_lce_req                 = 4'b1010
  ,e_mux_sel_lce_lce_resp                = 4'b1011
  ,e_mux_sel_lce_mem_resp                = 4'b1100
  ,e_mux_sel_lce_pending                 = 4'b1101
  ,e_mux_sel_lce_0                       = 4'b1111 // constant 0
} bp_cce_inst_mux_sel_lce_e;



// Way
typedef enum logic [3:0] {
  e_mux_sel_way_r0                       = 4'b0000
  ,e_mux_sel_way_r1                      = 4'b0001
  ,e_mux_sel_way_r2                      = 4'b0010
  ,e_mux_sel_way_r3                      = 4'b0011
  ,e_mux_sel_way_r4                      = 4'b0100
  ,e_mux_sel_way_r5                      = 4'b0101
  ,e_mux_sel_way_r6                      = 4'b0110
  ,e_mux_sel_way_r7                      = 4'b0111
  ,e_mux_sel_way_mshr_req                = 4'b1000
  ,e_mux_sel_way_mshr_owner              = 4'b1001
  ,e_mux_sel_way_mshr_lru                = 4'b1010
  ,e_mux_sel_way_sh_way                  = 4'b1011 // Sharer's vector ways, indexed by src_a
  ,e_mux_sel_way_0                       = 4'b1111 // constant 0
} bp_cce_inst_mux_sel_way_e;



// Coherence State
// source select for directory coherence state input
typedef enum logic [3:0] {
  e_mux_sel_coh_r0                       = 4'b0000
  ,e_mux_sel_coh_r1                      = 4'b0001
  ,e_mux_sel_coh_r2                      = 4'b0010
  ,e_mux_sel_coh_r3                      = 4'b0011
  ,e_mux_sel_coh_r4                      = 4'b0100
  ,e_mux_sel_coh_r5                      = 4'b0101
  ,e_mux_sel_coh_r6                      = 4'b0110
  ,e_mux_sel_coh_r7                      = 4'b0111
  ,e_mux_sel_coh_next_coh_state          = 4'b1000
  ,e_mux_sel_coh_lru_coh_state           = 4'b1001
  ,e_mux_sel_sharer_state                = 4'b1010 // Sharer's vector states, indexed by src_a
  ,e_mux_sel_coh_owner_coh_state         = 4'b1011
  ,e_mux_sel_coh_inst_imm                = 4'b1111
} bp_cce_inst_mux_sel_coh_state_e;



/*
 * Source and Destination Queue Selects and One-hot masks
 */

// Source queue one hot
// order: {lceReq, lceResp, memResp, pending}
typedef enum logic [3:0] {
  e_src_q_pending                        = 4'b0001
  ,e_src_q_mem_resp                      = 4'b0010
  ,e_src_q_lce_resp                      = 4'b0100
  ,e_src_q_lce_req                       = 4'b1000
} bp_cce_inst_src_q_e;



// Source queue select
typedef enum logic [1:0] {
  e_src_q_sel_lce_req                    = 2'b00
  ,e_src_q_sel_mem_resp                  = 2'b01
  ,e_src_q_sel_pending                   = 2'b10
  ,e_src_q_sel_lce_resp                  = 2'b11
} bp_cce_inst_src_q_sel_e;



// Destination queue one hot
typedef enum logic [1:0] {
  e_dst_q_lce_cmd                        = 2'b01
  ,e_dst_q_mem_cmd                       = 2'b10
} bp_cce_inst_dst_q_e;



// Destination queue select
typedef enum logic [1:0] {
  e_dst_q_sel_lce_cmd                    = 2'b00
  ,e_dst_q_sel_mem_cmd                   = 2'b01
} bp_cce_inst_dst_q_sel_e;



/*
 * Instruction Struct Definitions
 *
 * Each instruction is 32-bits wide. There are also two metadata bits attached to each
 * instruction that indicate if the instruction is a branch and if the branch should
 * be predicted taken or not. The metadata bits enable the pre-decoder to quickly decide
 * what PC should be (speculatively) fetched next.
 *
 * Each instruction contains:
 *   op (3-bits)
 *   minor_op (4-bits)
 *   instruction type specific struct with padding (25-bits)
 *
 * Any changes made to this file must be reflected in the C version used by the assembler, and
 * in the assembler itself.
 *
 */




/*
 * 2-Register Encoding
 *
 */




typedef struct packed {
  logic [(
  (32-3-4)
-4 
  -(2*4))
-1:0]     pad;
  bp_cce_inst_src_u                      src_b;
  bp_cce_inst_dst_u                      dst;
  bp_cce_inst_src_u                      src_a;
} bp_cce_inst_rtype_s;

/*
 * Immediate Encoding
 *
 */




typedef struct packed {
  logic [16-1:0]   imm;
  logic [(
  (32-3-4)
-4 
  -4-16)
-1:0]     pad;
  bp_cce_inst_dst_u                      dst;
  bp_cce_inst_src_u                      src_a;
} bp_cce_inst_itype_s;

/*
 * Memory Load Encoding (same as I-Type)
 * rd = mem[ra+imm]
 *
 * Src and dst can only be GPR
 */

// no padding needed

typedef struct packed {
  logic [16-1:0]   imm;
  logic                                  global_mem;
  bp_cce_inst_opd_gpr_e                  dst;
  bp_cce_inst_opd_gpr_e                  src_a;
} bp_cce_inst_mltype_s;

/*
 * Memory Store Encoding (basically I-Type, but second source instead of destination)
 * mem[ra+imm] = rb
 *
 * Src and dst can only be GPR
 */

// no padding needed

typedef struct packed {
  logic [16-1:0]   imm;
  logic                                  global_mem;
  bp_cce_inst_opd_gpr_e                  src_b;
  bp_cce_inst_opd_gpr_e                  src_a;
} bp_cce_inst_mstype_s;

/*
 * Branch Encoding
 *
 */




typedef struct packed {
  logic [9-1:0]    target;
  logic [(
  (32-3-4)
-4 
  -(2*4)-9)
-1:0]     pad;
  bp_cce_inst_src_u                      src_b;
  logic [4-1:0]    pad4;
  bp_cce_inst_src_u                      src_a;
} bp_cce_inst_btype_s;

/*
 * Branch-Immediate Encoding
 *
 */




typedef struct packed {
  logic [9-1:0]    target;
  logic [(
  (32-3-4)
-4 
  -8-9)
-1:0]    pad;
  logic [8-1:0]    imm;
  bp_cce_inst_src_u                      src_a;
} bp_cce_inst_bitype_s;

/*
 * Branch-Flag Encoding
 *
 */

// no padding, target and immediate occupy exactly 25 bits

typedef struct packed {
  logic [9-1:0]    target;
  logic [16-1:0]   imm;
} bp_cce_inst_bftype_s;

/*
 * SpecQ Encoding (S-Type)
 *
 */




typedef struct packed {
  logic [(
  (32-3-4)
-$bits(bp_cce_inst_spec_op_e) 
  -$bits(bp_cce_inst_mux_sel_addr_e)-$bits(bp_coh_states_e)-4)
-1:0]     pad;
  bp_coh_states_e                        state;
  bp_cce_inst_mux_sel_addr_e             addr_sel;
  bp_cce_inst_opd_gpr_e                  dst;
  bp_cce_inst_spec_op_e                  cmd;
} bp_cce_inst_stype_s;

/*
 * Directory Pending Encoding (DP-Type)
 *
 */




typedef struct packed {
  logic [(
  (32-3-4)
-$bits(bp_cce_inst_mux_sel_addr_e) 
  -4-1)
-1:0]    pad;
  logic                                  pending;
  bp_cce_inst_opd_gpr_e                  dst;
  bp_cce_inst_mux_sel_addr_e             addr_sel;
} bp_cce_inst_dptype_s;

/*
 * Directory Read Encoding (DR-Type)
 *
 */





typedef struct packed {
  logic [(
  (32-3-4)
-$bits(bp_cce_inst_mux_sel_addr_e) 
  -$bits(bp_cce_inst_mux_sel_lce_e)-(2*$bits(bp_cce_inst_mux_sel_way_e)) 
  -(2*4))
-1:0]    pad;
  bp_cce_inst_opd_gpr_e                  src_a;
  bp_cce_inst_mux_sel_way_e              lru_way_sel;
  bp_cce_inst_mux_sel_way_e              way_sel;
  bp_cce_inst_mux_sel_lce_e              lce_sel;
  bp_cce_inst_opd_gpr_e                  dst;
  bp_cce_inst_mux_sel_addr_e             addr_sel;
} bp_cce_inst_drtype_s;

/*
 * Directory Write Encoding (DW-Type)
 *
 */





typedef struct packed {
  logic [(
  (32-3-4)
-$bits(bp_cce_inst_mux_sel_addr_e) 
  -$bits(bp_cce_inst_mux_sel_lce_e)-$bits(bp_cce_inst_mux_sel_way_e) 
  -$bits(bp_cce_inst_mux_sel_coh_state_e)-$bits(bp_coh_states_e)-4)
-1:0]    pad;
  bp_cce_inst_opd_gpr_e                  src_a;
  bp_coh_states_e                        state;
  bp_cce_inst_mux_sel_way_e              way_sel;
  bp_cce_inst_mux_sel_lce_e              lce_sel;
  bp_cce_inst_mux_sel_coh_state_e        state_sel;
  bp_cce_inst_mux_sel_addr_e             addr_sel;
} bp_cce_inst_dwtype_s;

/*
 * Pop Queue Encoding
 *
 */




typedef struct packed {
  logic                                  write_pending;
  logic [(
  (32-3-4)
-$bits(bp_cce_inst_src_q_sel_e) 
  -4-2-1)
-1:0]      pad;
  bp_cce_inst_opd_gpr_e                  dst;
  logic [2-1:0]    pad2;
  bp_cce_inst_src_q_sel_e                src_q;
} bp_cce_inst_popq_s;

/*
 * Push Queue Encoding
 *
 */

// no padding, all bits used

typedef struct packed {
  logic                                  write_pending;
  union packed
  {
    bp_cce_inst_mux_sel_way_e                    way_sel;
    // msg_size field must be same or fewer bits than way_sel field
    // currently, msg_size requires 3 bits to hold bp_mem_msg_size_e from
    // bp_common_lce_cce_if.svh
    logic [$bits(bp_cce_inst_mux_sel_way_e)-1:0] msg_size;
  }                                      way_or_size;
  bp_cce_inst_opd_gpr_e                  src_a;
  bp_cce_inst_mux_sel_lce_e              lce_sel;
  bp_cce_inst_mux_sel_addr_e             addr_sel;
  union packed
  {
    bp_bedrock_cmd_type_e         lce_cmd;
    bp_bedrock_mem_type_e         mem_cmd;
  }                                      cmd;
  logic                                  spec;
  logic                                  custom;
  bp_cce_inst_dst_q_sel_e                dst_q;
} bp_cce_inst_pushq_s;

/*
 * Instruction Type Struct Union
 */

typedef union packed {
  bp_cce_inst_rtype_s                    rtype;
  bp_cce_inst_itype_s                    itype;
  bp_cce_inst_mltype_s                   mltype;
  bp_cce_inst_mstype_s                   mstype;
  bp_cce_inst_btype_s                    btype;
  bp_cce_inst_bitype_s                   bitype;
  bp_cce_inst_bftype_s                   bftype;
  bp_cce_inst_stype_s                    stype;
  bp_cce_inst_dptype_s                   dptype;
  bp_cce_inst_dwtype_s                   dwtype;
  bp_cce_inst_drtype_s                   drtype;
  bp_cce_inst_popq_s                     popq;
  bp_cce_inst_pushq_s                    pushq;
} bp_cce_inst_type_u;

typedef struct packed {
  logic                                  predict_taken;
  logic                                  branch;
  bp_cce_inst_type_u                     type_u;
  bp_cce_inst_minor_op_u                 minor_op_u;
  bp_cce_inst_op_e                       op;
} bp_cce_inst_s;



/*
 * bp_cce_inst_decoded_s defines the decoded form of the CCE microcode instructions
 *
 */
typedef struct packed {

  // instruction is valid
  logic                                    v;

  // branch and predict taken bits from raw instruction
  logic                                    branch;
  logic                                    predict_taken;

  // Basic operation information
  bp_cce_inst_op_e                         op;
  bp_cce_inst_minor_op_u                   minor_op_u;

  // Destination and Source signals with selects
  bp_cce_inst_dst_u                        dst;
  bp_cce_inst_dst_sel_e                    dst_sel;
  bp_cce_inst_src_u                        src_a;
  bp_cce_inst_src_sel_e                    src_a_sel;
  bp_cce_inst_src_u                        src_b;
  bp_cce_inst_src_sel_e                    src_b_sel;

  // Address, LCE, Way, and Coherence State Selects
  // These are used by directory, pending bits, speculative bits, messages, etc.
  // note: addr_bypass signal generated by src_sel depending on mux signal
  // bypass will occur for GPR as source
  bp_cce_inst_mux_sel_addr_e               addr_sel;
  bp_cce_inst_mux_sel_lce_e                lce_sel;
  bp_cce_inst_mux_sel_way_e                way_sel;
  bp_cce_inst_mux_sel_way_e                lru_way_sel;
  bp_cce_inst_mux_sel_coh_state_e          coh_state_sel;

  // Immediate
  logic [64-1:0]       imm;

  // ALU Unit
  bp_cce_inst_alu_op_e                     alu_op;

  // Branch Unit
  bp_cce_inst_branch_op_e                  branch_op;
  logic [9-1:0]      branch_target;

  // Directory
  logic                                    dir_r_v;
  logic                                    dir_w_v;

  // GAD Module
  logic                                    gad_v;

  // WFQ
  logic                                    wfq_v;

  // Pending Bits
  logic                                    pending_r_v;
  logic                                    pending_w_v;
  logic                                    pending_bit;
  logic                                    pending_clear;

  // Speculative Memory Access Bits
  logic                                    spec_r_v;
  logic                                    spec_w_v;
  logic                                    spec_v;
  logic                                    spec_squash_v;
  logic                                    spec_fwd_mod_v;
  logic                                    spec_state_v;
  bp_cce_spec_s                            spec_bits;

  // Message Unit / Messages
  logic                                    poph;
  logic                                    popq;
  logic                                    popd;
  logic                                    pushq;
  logic                                    pushq_custom;
  bp_bedrock_msg_size_e                    msg_size;
  bp_cce_inst_dst_q_sel_e                  pushq_qsel;
  bp_cce_inst_src_q_sel_e                  popq_qsel;
  logic                                    lce_req_yumi;
  logic                                    lce_resp_yumi;
  logic                                    mem_resp_yumi;
  logic                                    pending_yumi;
  logic                                    lce_cmd_v;
  bp_bedrock_cmd_type_e                    lce_cmd;
  logic                                    mem_cmd_v;
  bp_bedrock_mem_type_e                    mem_cmd;
  logic                                    inv_cmd_v;

  // GPR write mask
  logic [8-1:0]         gpr_w_v;

  // MSHR write signals
  logic                                    mshr_clear;
  logic                                    lce_w_v;
  logic                                    addr_w_v;
  logic                                    way_w_v;
  logic                                    lru_addr_w_v;
  logic                                    lru_way_w_v;
  logic                                    owner_lce_w_v;
  logic                                    owner_way_w_v;
  logic                                    next_coh_state_w_v;
  logic                                    lru_coh_state_w_v;
  logic                                    owner_coh_state_w_v;
  // Flag write mask - for instructions that write flags, e.g., GAD, poph, mov, sf
  logic [$bits(bp_cce_inst_flag_onehot_e)-1:0]       flag_w_v;
  logic                                    msg_size_w_v;
  // Special/Param registers
  logic                                    coh_state_w_v;
  logic                                    auto_fwd_msg_w_v;

  // stall counter
  logic                                    clr_stall_cnt;

} bp_cce_inst_decoded_s;






  

  localparam mem_cmd_payload_mask_gp  = (1 << e_bedrock_mem_uc_wr) | (1 << e_bedrock_mem_wr);
  localparam mem_resp_payload_mask_gp = (1 << e_bedrock_mem_uc_rd) | (1 << e_bedrock_mem_rd);

  // Miss Status Handling Register Struct
  // This struct tracks the information required to process an LCE request
  
endpackage : bp_me_pkg

package bsg_noc_pkg;
  // Explictly sizing enum values (P=3'd0, not P=0) is necessary per Verilator 4.015
  // https://www.veripool.org/issues/1442-Verilator-Enum-values-without-explicit-widths-are-considered-unsized
  typedef enum logic[2:0] {P=3'd0, W, E, N, S} Dirs;
endpackage

   
module bp_me_nonsynth_lce_tracer
  import bp_common_pkg::*;
  import bp_common_aviary_pkg::*;
  import bp_me_nonsynth_pkg::*;
  #(parameter bp_params_e bp_params_p = e_bp_unicore_half_cfg
    
  , localparam bp_proc_param_s proc_param_lp = all_cfgs_gp[bp_params_p]                         
                                                                                                   
  , localparam multicore_p = proc_param_lp.multicore                                               
                                                                                                   
  , localparam cc_x_dim_p  = proc_param_lp.cc_x_dim                                                
  , localparam cc_y_dim_p  = proc_param_lp.cc_y_dim                                                
                                                                                                   
  , localparam ic_x_dim_p = cc_x_dim_p                                                             
  , localparam ic_y_dim_p = proc_param_lp.ic_y_dim                                                 
  , localparam mc_x_dim_p = cc_x_dim_p                                                             
  , localparam mc_y_dim_p = proc_param_lp.mc_y_dim                                                 
  , localparam cac_x_dim_p = proc_param_lp.cac_x_dim                                               
  , localparam cac_y_dim_p = cc_y_dim_p                                                            
  , localparam sac_x_dim_p = proc_param_lp.sac_x_dim                                               
  , localparam sac_y_dim_p = cc_y_dim_p                                                            
  , localparam cacc_type_p = proc_param_lp.cacc_type                                               
  , localparam sacc_type_p = proc_param_lp.sacc_type                                               
                                                                                                   
  , localparam num_core_p  = cc_x_dim_p * cc_y_dim_p                                               
  , localparam num_io_p    = ic_x_dim_p * ic_y_dim_p                                               
  , localparam num_l2e_p   = mc_x_dim_p * mc_y_dim_p                                               
  , localparam num_cacc_p  = cac_x_dim_p * cac_y_dim_p                                             
  , localparam num_sacc_p  = sac_x_dim_p * sac_y_dim_p                                             
                                                                                                   
  , localparam num_cce_p = proc_param_lp.num_cce                                                   
  , localparam num_lce_p = proc_param_lp.num_lce                                                   
                                                                                                   
  , localparam core_id_width_p = ( ((cc_x_dim_p*cc_y_dim_p)==1) ? 1 : $clog2((cc_x_dim_p*cc_y_dim_p)))                            
  , localparam cce_id_width_p  = ( (((cc_x_dim_p*1+2)*(cc_y_dim_p*1+2))==1) ? 1 : $clog2(((cc_x_dim_p*1+2)*(cc_y_dim_p*1+2))))                
  , localparam lce_id_width_p  = ( (((cc_x_dim_p*2+2)*(cc_y_dim_p*2+2))==1) ? 1 : $clog2(((cc_x_dim_p*2+2)*(cc_y_dim_p*2+2))))                
                                                                                                   
  , localparam vaddr_width_p = proc_param_lp.vaddr_width                                           
  , localparam paddr_width_p = proc_param_lp.paddr_width                                           
  , localparam asid_width_p  = proc_param_lp.asid_width                                            
                                                                                                   
  , localparam boot_pc_p       = proc_param_lp.boot_pc                                             
  , localparam boot_in_debug_p = proc_param_lp.boot_in_debug                                       
                                                                                                   
  , localparam branch_metadata_fwd_width_p = proc_param_lp.branch_metadata_fwd_width               
  , localparam btb_tag_width_p             = proc_param_lp.btb_tag_width                           
  , localparam btb_idx_width_p             = proc_param_lp.btb_idx_width                           
  , localparam bht_idx_width_p             = proc_param_lp.bht_idx_width                           
  , localparam ghist_width_p               = proc_param_lp.ghist_width                             
                                                                                                   
  , localparam itlb_els_p              = proc_param_lp.itlb_els                                    
  , localparam dtlb_els_p              = proc_param_lp.dtlb_els                                    
                                                                                                   
  , localparam lr_sc_p                    = proc_param_lp.lr_sc                                    
  , localparam amo_swap_p                 = proc_param_lp.amo_swap                                 
  , localparam amo_fetch_logic_p          = proc_param_lp.amo_fetch_logic                          
  , localparam amo_fetch_arithmetic_p     = proc_param_lp.amo_fetch_arithmetic                     
                                                                                                   
  , localparam l1_coherent_p              = proc_param_lp.l1_coherent                              
  , localparam l1_writethrough_p          = proc_param_lp.l1_writethrough                          
  , localparam dcache_sets_p              = proc_param_lp.dcache_sets                              
  , localparam dcache_assoc_p             = proc_param_lp.dcache_assoc                             
  , localparam dcache_block_width_p       = proc_param_lp.dcache_block_width                       
  , localparam dcache_fill_width_p        = proc_param_lp.dcache_fill_width                        
  , localparam icache_sets_p              = proc_param_lp.icache_sets                              
  , localparam icache_assoc_p             = proc_param_lp.icache_assoc                             
  , localparam icache_block_width_p       = proc_param_lp.icache_block_width                       
  , localparam icache_fill_width_p        = proc_param_lp.icache_fill_width                        
  , localparam acache_sets_p              = proc_param_lp.acache_sets                              
  , localparam acache_assoc_p             = proc_param_lp.acache_assoc                             
  , localparam acache_block_width_p       = proc_param_lp.acache_block_width                       
  , localparam acache_fill_width_p        = proc_param_lp.acache_fill_width                        
  , localparam lce_assoc_p                = (((dcache_assoc_p)>(                               
                                                     (((icache_assoc_p)>(acache_assoc_p)) ? (icache_assoc_p) : (acache_assoc_p)))) ? (dcache_assoc_p) : (                               
                                                     (((icache_assoc_p)>(acache_assoc_p)) ? (icache_assoc_p) : (acache_assoc_p))))
     
  , localparam lce_assoc_width_p          = ( ((lce_assoc_p)==1) ? 1 : $clog2((lce_assoc_p)))                           
  , localparam lce_sets_p                 = (((dcache_sets_p)>(                                
                                                     (((icache_sets_p)>(acache_sets_p)) ? (icache_sets_p) : (acache_sets_p)))) ? (dcache_sets_p) : (                                
                                                     (((icache_sets_p)>(acache_sets_p)) ? (icache_sets_p) : (acache_sets_p))))
       
  , localparam lce_sets_width_p           = ( ((lce_sets_p)==1) ? 1 : $clog2((lce_sets_p)))                            
                                                                                                   
  , localparam cce_block_width_p          =  (((dcache_block_width_p)>(                        
                                                     (((icache_block_width_p)>(                
                                                       acache_block_width_p)) ? (icache_block_width_p) : (                
                                                       acache_block_width_p))
)) ? (dcache_block_width_p) : (                        
                                                     (((icache_block_width_p)>(                
                                                       acache_block_width_p)) ? (icache_block_width_p) : (                
                                                       acache_block_width_p))
))
                      
                                                                                                   
                                                                                                   
  , localparam cce_pc_width_p             = proc_param_lp.cce_pc_width                             
  , localparam num_cce_instr_ram_els_p    = 2**cce_pc_width_p                                      
  , localparam cce_way_groups_p           = (((dcache_sets_p)>(icache_sets_p)) ? (dcache_sets_p) : (icache_sets_p))                 
  , localparam cce_instr_width_p          = 34 
  , localparam cce_ucode_p                = proc_param_lp.cce_ucode                                
                                                                                                   
  , localparam l2_en_p    = proc_param_lp.l2_en                                                    
  , localparam l2_sets_p  = proc_param_lp.l2_sets                                                  
  , localparam l2_assoc_p = proc_param_lp.l2_assoc                                                 
  , localparam l2_outstanding_reqs_p = proc_param_lp.l2_outstanding_reqs                           
                                                                                                   
  , localparam fe_queue_fifo_els_p = proc_param_lp.fe_queue_fifo_els                               
  , localparam fe_cmd_fifo_els_p   = proc_param_lp.fe_cmd_fifo_els                                 
                                                                                                   
  , localparam async_coh_clk_p        = proc_param_lp.async_coh_clk                                
  , localparam coh_noc_max_credits_p  = proc_param_lp.coh_noc_max_credits                          
  , localparam coh_noc_flit_width_p   = proc_param_lp.coh_noc_flit_width                           
  , localparam coh_noc_cid_width_p    = proc_param_lp.coh_noc_cid_width                            
  , localparam coh_noc_len_width_p    = proc_param_lp.coh_noc_len_width                            
  , localparam coh_noc_y_cord_width_p = ( ((ic_y_dim_p+cc_y_dim_p+mc_y_dim_p+1)==1) ? 1 : $clog2((ic_y_dim_p+cc_y_dim_p+mc_y_dim_p+1)))        
  , localparam coh_noc_x_cord_width_p = ( ((sac_x_dim_p+cc_x_dim_p+cac_x_dim_p+1)==1) ? 1 : $clog2((sac_x_dim_p+cc_x_dim_p+cac_x_dim_p+1)))      
  , localparam coh_noc_dims_p         = 2 
  , localparam coh_noc_dirs_p         = coh_noc_dims_p*2 + 1 
  , localparam coh_noc_trans_p        = 0 
  , localparam int coh_noc_cord_markers_pos_p[coh_noc_dims_p:0] = coh_noc_trans_p                  
      ? '{coh_noc_x_cord_width_p+coh_noc_y_cord_width_p, coh_noc_y_cord_width_p, 0}                
      : '{coh_noc_y_cord_width_p+coh_noc_x_cord_width_p, coh_noc_x_cord_width_p, 0}                
  , localparam coh_noc_cord_width_p   = coh_noc_cord_markers_pos_p[coh_noc_dims_p]                 
                                                                                                   
  , localparam async_mem_clk_p           = proc_param_lp.async_mem_clk                             
  , localparam mem_noc_max_credits_p     = proc_param_lp.mem_noc_max_credits                       
  , localparam mem_noc_flit_width_p      = proc_param_lp.mem_noc_flit_width                        
  , localparam mem_noc_cid_width_p       = proc_param_lp.mem_noc_cid_width                         
  , localparam mem_noc_len_width_p       = proc_param_lp.mem_noc_len_width                         
  , localparam mem_noc_y_cord_width_p    = ( ((ic_y_dim_p+cc_y_dim_p+mc_y_dim_p+1)==1) ? 1 : $clog2((ic_y_dim_p+cc_y_dim_p+mc_y_dim_p+1)))     
  , localparam mem_noc_x_cord_width_p    = 0 
  , localparam mem_noc_dims_p            = 1 
  , localparam mem_noc_cord_dims_p       = 2 
  , localparam mem_noc_dirs_p            = mem_noc_dims_p*2 + 1 
  , localparam mem_noc_trans_p           = 1 
  , localparam int mem_noc_cord_markers_pos_p[mem_noc_cord_dims_p:0] = mem_noc_trans_p             
      ? '{mem_noc_x_cord_width_p+mem_noc_y_cord_width_p, mem_noc_y_cord_width_p, 0}                
      : '{mem_noc_y_cord_width_p+mem_noc_x_cord_width_p, mem_noc_x_cord_width_p, 0}                
  , localparam mem_noc_cord_width_p      = mem_noc_cord_markers_pos_p[mem_noc_dims_p]              
                                                                                                   
  , localparam async_io_clk_p           = proc_param_lp.async_io_clk                               
  , localparam io_noc_max_credits_p     = proc_param_lp.io_noc_max_credits                         
  , localparam io_noc_did_width_p       = proc_param_lp.io_noc_did_width                           
  , localparam io_noc_flit_width_p      = proc_param_lp.io_noc_flit_width                          
  , localparam io_noc_cid_width_p       = proc_param_lp.io_noc_cid_width                           
  , localparam io_noc_len_width_p       = proc_param_lp.io_noc_len_width                           
  , localparam io_noc_y_cord_width_p    = 0 
  , localparam io_noc_x_cord_width_p    = io_noc_did_width_p                                       
  , localparam io_noc_dims_p            = 1 
  , localparam io_noc_cord_dims_p       = 2 
  , localparam io_noc_dirs_p            = io_noc_cord_dims_p*2 + 1 
  , localparam io_noc_trans_p           = 0 
  , localparam int io_noc_cord_markers_pos_p[io_noc_cord_dims_p:0] = io_noc_trans_p                
      ? '{io_noc_x_cord_width_p+io_noc_y_cord_width_p, io_noc_y_cord_width_p, 0}                   
      : '{io_noc_y_cord_width_p+io_noc_x_cord_width_p, io_noc_x_cord_width_p, 0}                   
  , localparam io_noc_cord_width_p      = io_noc_cord_markers_pos_p[io_noc_dims_p]                 
                                                                                                   
  , localparam dword_width_p       = 64 
  , localparam word_width_p        = 32 
  , localparam instr_width_p       = 32 
  , localparam csr_addr_width_p    = 12 
  , localparam reg_addr_width_p    = 5 
  , localparam page_offset_width_p = 12 
                                                                                                   
  , localparam vtag_width_p  = proc_param_lp.vaddr_width - page_offset_width_p                     
  , localparam ptag_width_p  = proc_param_lp.paddr_width - page_offset_width_p                     


    , parameter sets_p = "inv"
    , parameter assoc_p = "inv"
    , parameter block_width_p = "inv"

    , localparam lce_trace_file_p = "lce"

    , localparam block_size_in_bytes_lp=(block_width_p / 8)

    , localparam block_offset_bits_lp=( ((block_size_in_bytes_lp)==1) ? 1 : $clog2((block_size_in_bytes_lp)))

    , localparam lg_sets_lp=( ((sets_p)==1) ? 1 : $clog2((sets_p)))
    , localparam lg_assoc_lp=( ((assoc_p)==1) ? 1 : $clog2((assoc_p)))

    , localparam ptag_width_lp=(paddr_width_p-lg_sets_lp-block_offset_bits_lp)

    , localparam lg_num_cce_lp=( ((num_cce_p)==1) ? 1 : $clog2((num_cce_p)))

    , localparam lce_req_data_width_lp = dword_width_p

    
  
  , localparam lce_req_payload_width_lp = 
  (cce_id_width_p+lce_id_width_p+$bits(bp_bedrock_req_non_excl_e)+( ((lce_assoc_p)==1) ? 1 : $clog2((lce_assoc_p))))
 
  , localparam lce_cmd_payload_width_lp = 
  ((2*lce_id_width_p)+cce_id_width_p+(2*( ((lce_assoc_p)==1) ? 1 : $clog2((lce_assoc_p))))+(2*$bits(bp_coh_states_e)))
 
  , localparam lce_resp_payload_width_lp = 
  (cce_id_width_p+lce_id_width_p)

                               
  
  , localparam lce_req_msg_header_width_lp = 
  ($bits(bp_bedrock_msg_u)+paddr_width_p+$bits(bp_bedrock_msg_size_e)+lce_req_payload_width_lp)

             
  
  , localparam lce_cmd_msg_header_width_lp = 
  ($bits(bp_bedrock_msg_u)+paddr_width_p+$bits(bp_bedrock_msg_size_e)+lce_cmd_payload_width_lp)

             
  
  , localparam lce_resp_msg_header_width_lp = 
  ($bits(bp_bedrock_msg_u)+paddr_width_p+$bits(bp_bedrock_msg_size_e)+lce_resp_payload_width_lp)

           
  
  , localparam lce_req_msg_width_lp = 
  (
  ($bits(bp_bedrock_msg_u)+paddr_width_p+$bits(bp_bedrock_msg_size_e)+lce_req_payload_width_lp)
+cce_block_width_p)

     
  
  , localparam lce_cmd_msg_width_lp = 
  (
  ($bits(bp_bedrock_msg_u)+paddr_width_p+$bits(bp_bedrock_msg_size_e)+lce_cmd_payload_width_lp)
+cce_block_width_p)

     
  
  , localparam lce_resp_msg_width_lp = 
  (
  ($bits(bp_bedrock_msg_u)+paddr_width_p+$bits(bp_bedrock_msg_size_e)+lce_resp_payload_width_lp)
+cce_block_width_p)



  )
  (
    input                                                   clk_i
    ,input                                                  reset_i

    ,input [lce_id_width_p-1:0]                             lce_id_i

    // LCE-CCE Interface
    ,input [lce_req_msg_width_lp-1:0]                       lce_req_i
    ,input                                                  lce_req_v_i
    ,input                                                  lce_req_ready_i

    ,input [lce_resp_msg_width_lp-1:0]                      lce_resp_i
    ,input                                                  lce_resp_v_i
    ,input                                                  lce_resp_ready_i

    ,input [lce_cmd_msg_width_lp-1:0]                       lce_cmd_i
    ,input                                                  lce_cmd_v_i
    ,input                                                  lce_cmd_yumi_i

    ,input [lce_cmd_msg_width_lp-1:0]                       lce_cmd_o_i
    ,input                                                  lce_cmd_o_v_i
    ,input                                                  lce_cmd_o_ready_i
  );

  // LCE-CCE interface structs
  
  
                                                                                     
  typedef struct packed                                                              
  {                                                                                  
    logic [( ((lce_assoc_p)==1) ? 1 : $clog2((lce_assoc_p)))-1:0]    lru_way_id;                         
    bp_bedrock_req_non_excl_e                    non_exclusive;                      
    logic [lce_id_width_p-1:0]                  src_id;                             
    logic [cce_id_width_p-1:0]                  dst_id;                             
  } bp_bedrock_lce_req_payload_s;                                            
                                                                                     
  typedef struct packed                                                              
  {                                                                                  
    bp_coh_states_e                              target_state;                       
    logic [( ((lce_assoc_p)==1) ? 1 : $clog2((lce_assoc_p)))-1:0]    target_way_id;                      
    logic [lce_id_width_p-1:0]                  target;                             
    bp_coh_states_e                              state;                              
    logic [( ((lce_assoc_p)==1) ? 1 : $clog2((lce_assoc_p)))-1:0]    way_id;                             
    logic [cce_id_width_p-1:0]                  src_id;                             
    logic [lce_id_width_p-1:0]                  dst_id;                             
  } bp_bedrock_lce_cmd_payload_s;                                            
                                                                                     
  typedef struct packed                                                              
  {                                                                                  
    logic [lce_id_width_p-1:0]                  src_id;                             
    logic [cce_id_width_p-1:0]                  dst_id;                             
  } bp_bedrock_lce_resp_payload_s;                                           
;                            
  
  typedef struct packed                                                                   
  {                                                                                       
    logic [lce_req_payload_width_lp-1:0]                 payload;                                 
    bp_bedrock_msg_size_e                        size;                                    
    logic [paddr_width_p-1:0]                    addr;                                    
    bp_bedrock_msg_u                             msg_type;                                
  } bp_bedrock_lce_req_msg_header_s;                                                  
                                                                                          
  typedef struct packed                                                                   
  {                                                                                       
    logic [cce_block_width_p-1:0]                    data;                                    
    bp_bedrock_lce_req_msg_header_s          header;                                  
  } bp_bedrock_lce_req_msg_s;                                                         
; 
  
  typedef struct packed                                                                   
  {                                                                                       
    logic [lce_cmd_payload_width_lp-1:0]                 payload;                                 
    bp_bedrock_msg_size_e                        size;                                    
    logic [paddr_width_p-1:0]                    addr;                                    
    bp_bedrock_msg_u                             msg_type;                                
  } bp_bedrock_lce_cmd_msg_header_s;                                                  
                                                                                          
  typedef struct packed                                                                   
  {                                                                                       
    logic [cce_block_width_p-1:0]                    data;                                    
    bp_bedrock_lce_cmd_msg_header_s          header;                                  
  } bp_bedrock_lce_cmd_msg_s;                                                         
; 
  
  typedef struct packed                                                                   
  {                                                                                       
    logic [lce_resp_payload_width_lp-1:0]                 payload;                                 
    bp_bedrock_msg_size_e                        size;                                    
    logic [paddr_width_p-1:0]                    addr;                                    
    bp_bedrock_msg_u                             msg_type;                                
  } bp_bedrock_lce_resp_msg_header_s;                                                  
                                                                                          
  typedef struct packed                                                                   
  {                                                                                       
    logic [cce_block_width_p-1:0]                    data;                                    
    bp_bedrock_lce_resp_msg_header_s          header;                                  
  } bp_bedrock_lce_resp_msg_s;                                                         
;
;

  // Structs for output messages
  bp_bedrock_lce_req_msg_s  lce_req;
  bp_bedrock_lce_resp_msg_s lce_resp;
  bp_bedrock_lce_cmd_msg_s  lce_cmd, lce_cmd_lo;
  bp_bedrock_lce_req_payload_s  lce_req_payload;
  bp_bedrock_lce_resp_payload_s lce_resp_payload;
  bp_bedrock_lce_cmd_payload_s  lce_cmd_payload, lce_cmd_lo_payload;

  assign lce_req = lce_req_i;
  assign lce_resp = lce_resp_i;
  assign lce_cmd = lce_cmd_i;
  assign lce_cmd_lo = lce_cmd_o_i;
  assign lce_req_payload = lce_req.header.payload;
  assign lce_resp_payload = lce_resp.header.payload;
  assign lce_cmd_payload = lce_cmd.header.payload;
  assign lce_cmd_lo_payload = lce_cmd_lo.header.payload;

  integer file;
  string file_name;

  always_ff @(negedge reset_i) begin
    file_name = $sformatf("%s_%x.trace", lce_trace_file_p, lce_id_i);
    file      = $fopen(file_name, "w");
  end

  always_ff @(posedge clk_i) begin
    if (~reset_i) begin

      // LCE-CCE Interface

      // request to CCE
      if (lce_req_v_i & lce_req_ready_i) begin
        assert(lce_req_payload.src_id == lce_id_i) else $error("Bad LCE Request - source mismatch");
        $fdisplay(file, "[%t]: LCE[%0d] REQ addr[%H] cce[%0d] msg[%b] ne[%b] lru[%0d] size[%b] %H"
                  , $time, lce_req_payload.src_id, lce_req.header.addr, lce_req_payload.dst_id, lce_req.header.msg_type
                  , lce_req_payload.non_exclusive, lce_req_payload.lru_way_id
                  , lce_req.header.size, lce_req.data
                  );
      end

      // response to CCE
      if (lce_resp_v_i & lce_resp_ready_i) begin
        assert(lce_resp_payload.src_id == lce_id_i) else $error("Bad LCE Response - source mismatch");
        $fdisplay(file, "[%t]: LCE[%0d] RESP addr[%H] cce[%0d] msg[%b] len[%b] %H"
                  , $time, lce_resp_payload.src_id, lce_resp.header.addr, lce_resp_payload.dst_id, lce_resp.header.msg_type
                  , lce_resp.header.size, lce_resp.data
                  );
      end

      // command to LCE
      if (lce_cmd_v_i & lce_cmd_yumi_i) begin
        assert(lce_cmd_payload.dst_id == lce_id_i) else $error("Bad LCE Command - destination mismatch");
        $fdisplay(file, "[%t]: LCE[%0d] CMD IN addr[%H] cce[%0d] msg[%b] set[%0d] way[%0d] state[%b] tgt[%0d] tgt_way[%0d] len[%b] %H"
                  , $time, lce_cmd_payload.dst_id, lce_cmd.header.addr, lce_cmd_payload.src_id, lce_cmd.header.msg_type
                  , lce_cmd.header.addr[block_offset_bits_lp+:lg_sets_lp], lce_cmd_payload.way_id, lce_cmd_payload.state, lce_cmd_payload.target
                  , lce_cmd_payload.target_way_id, lce_cmd.header.size, lce_cmd.data
                  );
      end

      // command from LCE
      if (lce_cmd_o_v_i & lce_cmd_o_ready_i) begin
        $fdisplay(file, "[%t]: LCE[%0d] CMD OUT dst[%0d] addr[%H] CCE[%0d] msg[%b] way[%0d] state[%b] tgt[%0d] tgt_way[%0d] len[%b] %H"
                  , $time, lce_id_i, lce_cmd_lo_payload.dst_id, lce_cmd_lo.header.addr, lce_cmd_lo_payload.src_id, lce_cmd_lo.header.msg_type
                  , lce_cmd_lo_payload.way_id, lce_cmd_lo_payload.state, lce_cmd_lo_payload.target, lce_cmd_lo_payload.target_way_id
                  , lce_cmd_lo.header.size, lce_cmd_lo.data
                  );
      end

    end // ~reset_i
  end // always_ff

endmodule

module testbench
 import bp_common_pkg::*;
 import bp_common_aviary_pkg::*;
 import bp_be_pkg::*;
 import bp_me_pkg::*;
 import bsg_noc_pkg::*;
 #(parameter bp_params_e bp_params_p = e_bp_default_cfg // Replaced by the flow with a specific bp_cfg
   
  , localparam bp_proc_param_s proc_param_lp = all_cfgs_gp[bp_params_p]                         
                                                                                                   
  , localparam multicore_p = proc_param_lp.multicore                                               
                                                                                                   
  , localparam cc_x_dim_p  = proc_param_lp.cc_x_dim                                                
  , localparam cc_y_dim_p  = proc_param_lp.cc_y_dim                                                
                                                                                                   
  , localparam ic_x_dim_p = cc_x_dim_p                                                             
  , localparam ic_y_dim_p = proc_param_lp.ic_y_dim                                                 
  , localparam mc_x_dim_p = cc_x_dim_p                                                             
  , localparam mc_y_dim_p = proc_param_lp.mc_y_dim                                                 
  , localparam cac_x_dim_p = proc_param_lp.cac_x_dim                                               
  , localparam cac_y_dim_p = cc_y_dim_p                                                            
  , localparam sac_x_dim_p = proc_param_lp.sac_x_dim                                               
  , localparam sac_y_dim_p = cc_y_dim_p                                                            
  , localparam cacc_type_p = proc_param_lp.cacc_type                                               
  , localparam sacc_type_p = proc_param_lp.sacc_type                                               
                                                                                                   
  , localparam num_core_p  = cc_x_dim_p * cc_y_dim_p                                               
  , localparam num_io_p    = ic_x_dim_p * ic_y_dim_p                                               
  , localparam num_l2e_p   = mc_x_dim_p * mc_y_dim_p                                               
  , localparam num_cacc_p  = cac_x_dim_p * cac_y_dim_p                                             
  , localparam num_sacc_p  = sac_x_dim_p * sac_y_dim_p                                             
                                                                                                   
  , localparam num_cce_p = proc_param_lp.num_cce                                                   
  , localparam num_lce_p = proc_param_lp.num_lce                                                   
                                                                                                   
  , localparam core_id_width_p = ( ((cc_x_dim_p*cc_y_dim_p)==1) ? 1 : $clog2((cc_x_dim_p*cc_y_dim_p)))                            
  , localparam cce_id_width_p  = ( (((cc_x_dim_p*1+2)*(cc_y_dim_p*1+2))==1) ? 1 : $clog2(((cc_x_dim_p*1+2)*(cc_y_dim_p*1+2))))                
  , localparam lce_id_width_p  = ( (((cc_x_dim_p*2+2)*(cc_y_dim_p*2+2))==1) ? 1 : $clog2(((cc_x_dim_p*2+2)*(cc_y_dim_p*2+2))))                
                                                                                                   
  , localparam vaddr_width_p = proc_param_lp.vaddr_width                                           
  , localparam paddr_width_p = proc_param_lp.paddr_width                                           
  , localparam asid_width_p  = proc_param_lp.asid_width                                            
                                                                                                   
  , localparam boot_pc_p       = proc_param_lp.boot_pc                                             
  , localparam boot_in_debug_p = proc_param_lp.boot_in_debug                                       
                                                                                                   
  , localparam branch_metadata_fwd_width_p = proc_param_lp.branch_metadata_fwd_width               
  , localparam btb_tag_width_p             = proc_param_lp.btb_tag_width                           
  , localparam btb_idx_width_p             = proc_param_lp.btb_idx_width                           
  , localparam bht_idx_width_p             = proc_param_lp.bht_idx_width                           
  , localparam ghist_width_p               = proc_param_lp.ghist_width                             
                                                                                                   
  , localparam itlb_els_p              = proc_param_lp.itlb_els                                    
  , localparam dtlb_els_p              = proc_param_lp.dtlb_els                                    
                                                                                                   
  , localparam lr_sc_p                    = proc_param_lp.lr_sc                                    
  , localparam amo_swap_p                 = proc_param_lp.amo_swap                                 
  , localparam amo_fetch_logic_p          = proc_param_lp.amo_fetch_logic                          
  , localparam amo_fetch_arithmetic_p     = proc_param_lp.amo_fetch_arithmetic                     
                                                                                                   
  , localparam l1_coherent_p              = proc_param_lp.l1_coherent                              
  , localparam l1_writethrough_p          = proc_param_lp.l1_writethrough                          
  , localparam dcache_sets_p              = proc_param_lp.dcache_sets                              
  , localparam dcache_assoc_p             = proc_param_lp.dcache_assoc                             
  , localparam dcache_block_width_p       = proc_param_lp.dcache_block_width                       
  , localparam dcache_fill_width_p        = proc_param_lp.dcache_fill_width                        
  , localparam icache_sets_p              = proc_param_lp.icache_sets                              
  , localparam icache_assoc_p             = proc_param_lp.icache_assoc                             
  , localparam icache_block_width_p       = proc_param_lp.icache_block_width                       
  , localparam icache_fill_width_p        = proc_param_lp.icache_fill_width                        
  , localparam acache_sets_p              = proc_param_lp.acache_sets                              
  , localparam acache_assoc_p             = proc_param_lp.acache_assoc                             
  , localparam acache_block_width_p       = proc_param_lp.acache_block_width                       
  , localparam acache_fill_width_p        = proc_param_lp.acache_fill_width                        
  , localparam lce_assoc_p                = (((dcache_assoc_p)>(                               
                                                     (((icache_assoc_p)>(acache_assoc_p)) ? (icache_assoc_p) : (acache_assoc_p)))) ? (dcache_assoc_p) : (                               
                                                     (((icache_assoc_p)>(acache_assoc_p)) ? (icache_assoc_p) : (acache_assoc_p))))
     
  , localparam lce_assoc_width_p          = ( ((lce_assoc_p)==1) ? 1 : $clog2((lce_assoc_p)))                           
  , localparam lce_sets_p                 = (((dcache_sets_p)>(                                
                                                     (((icache_sets_p)>(acache_sets_p)) ? (icache_sets_p) : (acache_sets_p)))) ? (dcache_sets_p) : (                                
                                                     (((icache_sets_p)>(acache_sets_p)) ? (icache_sets_p) : (acache_sets_p))))
       
  , localparam lce_sets_width_p           = ( ((lce_sets_p)==1) ? 1 : $clog2((lce_sets_p)))                            
                                                                                                   
  , localparam cce_block_width_p          =  (((dcache_block_width_p)>(                        
                                                     (((icache_block_width_p)>(                
                                                       acache_block_width_p)) ? (icache_block_width_p) : (                
                                                       acache_block_width_p))
)) ? (dcache_block_width_p) : (                        
                                                     (((icache_block_width_p)>(                
                                                       acache_block_width_p)) ? (icache_block_width_p) : (                
                                                       acache_block_width_p))
))
                      
                                                                                                   
                                                                                                   
  , localparam cce_pc_width_p             = proc_param_lp.cce_pc_width                             
  , localparam num_cce_instr_ram_els_p    = 2**cce_pc_width_p                                      
  , localparam cce_way_groups_p           = (((dcache_sets_p)>(icache_sets_p)) ? (dcache_sets_p) : (icache_sets_p))                 
  , localparam cce_instr_width_p          = 34 
  , localparam cce_ucode_p                = proc_param_lp.cce_ucode                                
                                                                                                   
  , localparam l2_en_p    = proc_param_lp.l2_en                                                    
  , localparam l2_sets_p  = proc_param_lp.l2_sets                                                  
  , localparam l2_assoc_p = proc_param_lp.l2_assoc                                                 
  , localparam l2_outstanding_reqs_p = proc_param_lp.l2_outstanding_reqs                           
                                                                                                   
  , localparam fe_queue_fifo_els_p = proc_param_lp.fe_queue_fifo_els                               
  , localparam fe_cmd_fifo_els_p   = proc_param_lp.fe_cmd_fifo_els                                 
                                                                                                   
  , localparam async_coh_clk_p        = proc_param_lp.async_coh_clk                                
  , localparam coh_noc_max_credits_p  = proc_param_lp.coh_noc_max_credits                          
  , localparam coh_noc_flit_width_p   = proc_param_lp.coh_noc_flit_width                           
  , localparam coh_noc_cid_width_p    = proc_param_lp.coh_noc_cid_width                            
  , localparam coh_noc_len_width_p    = proc_param_lp.coh_noc_len_width                            
  , localparam coh_noc_y_cord_width_p = ( ((ic_y_dim_p+cc_y_dim_p+mc_y_dim_p+1)==1) ? 1 : $clog2((ic_y_dim_p+cc_y_dim_p+mc_y_dim_p+1)))        
  , localparam coh_noc_x_cord_width_p = ( ((sac_x_dim_p+cc_x_dim_p+cac_x_dim_p+1)==1) ? 1 : $clog2((sac_x_dim_p+cc_x_dim_p+cac_x_dim_p+1)))      
  , localparam coh_noc_dims_p         = 2 
  , localparam coh_noc_dirs_p         = coh_noc_dims_p*2 + 1 
  , localparam coh_noc_trans_p        = 0 
  , localparam int coh_noc_cord_markers_pos_p[coh_noc_dims_p:0] = coh_noc_trans_p                  
      ? '{coh_noc_x_cord_width_p+coh_noc_y_cord_width_p, coh_noc_y_cord_width_p, 0}                
      : '{coh_noc_y_cord_width_p+coh_noc_x_cord_width_p, coh_noc_x_cord_width_p, 0}                
  , localparam coh_noc_cord_width_p   = coh_noc_cord_markers_pos_p[coh_noc_dims_p]                 
                                                                                                   
  , localparam async_mem_clk_p           = proc_param_lp.async_mem_clk                             
  , localparam mem_noc_max_credits_p     = proc_param_lp.mem_noc_max_credits                       
  , localparam mem_noc_flit_width_p      = proc_param_lp.mem_noc_flit_width                        
  , localparam mem_noc_cid_width_p       = proc_param_lp.mem_noc_cid_width                         
  , localparam mem_noc_len_width_p       = proc_param_lp.mem_noc_len_width                         
  , localparam mem_noc_y_cord_width_p    = ( ((ic_y_dim_p+cc_y_dim_p+mc_y_dim_p+1)==1) ? 1 : $clog2((ic_y_dim_p+cc_y_dim_p+mc_y_dim_p+1)))     
  , localparam mem_noc_x_cord_width_p    = 0 
  , localparam mem_noc_dims_p            = 1 
  , localparam mem_noc_cord_dims_p       = 2 
  , localparam mem_noc_dirs_p            = mem_noc_dims_p*2 + 1 
  , localparam mem_noc_trans_p           = 1 
  , localparam int mem_noc_cord_markers_pos_p[mem_noc_cord_dims_p:0] = mem_noc_trans_p             
      ? '{mem_noc_x_cord_width_p+mem_noc_y_cord_width_p, mem_noc_y_cord_width_p, 0}                
      : '{mem_noc_y_cord_width_p+mem_noc_x_cord_width_p, mem_noc_x_cord_width_p, 0}                
  , localparam mem_noc_cord_width_p      = mem_noc_cord_markers_pos_p[mem_noc_dims_p]              
                                                                                                   
  , localparam async_io_clk_p           = proc_param_lp.async_io_clk                               
  , localparam io_noc_max_credits_p     = proc_param_lp.io_noc_max_credits                         
  , localparam io_noc_did_width_p       = proc_param_lp.io_noc_did_width                           
  , localparam io_noc_flit_width_p      = proc_param_lp.io_noc_flit_width                          
  , localparam io_noc_cid_width_p       = proc_param_lp.io_noc_cid_width                           
  , localparam io_noc_len_width_p       = proc_param_lp.io_noc_len_width                           
  , localparam io_noc_y_cord_width_p    = 0 
  , localparam io_noc_x_cord_width_p    = io_noc_did_width_p                                       
  , localparam io_noc_dims_p            = 1 
  , localparam io_noc_cord_dims_p       = 2 
  , localparam io_noc_dirs_p            = io_noc_cord_dims_p*2 + 1 
  , localparam io_noc_trans_p           = 0 
  , localparam int io_noc_cord_markers_pos_p[io_noc_cord_dims_p:0] = io_noc_trans_p                
      ? '{io_noc_x_cord_width_p+io_noc_y_cord_width_p, io_noc_y_cord_width_p, 0}                   
      : '{io_noc_y_cord_width_p+io_noc_x_cord_width_p, io_noc_x_cord_width_p, 0}                   
  , localparam io_noc_cord_width_p      = io_noc_cord_markers_pos_p[io_noc_dims_p]                 
                                                                                                   
  , localparam dword_width_p       = 64 
  , localparam word_width_p        = 32 
  , localparam instr_width_p       = 32 
  , localparam csr_addr_width_p    = 12 
  , localparam reg_addr_width_p    = 5 
  , localparam page_offset_width_p = 12 
                                                                                                   
  , localparam vtag_width_p  = proc_param_lp.vaddr_width - page_offset_width_p                     
  , localparam ptag_width_p  = proc_param_lp.paddr_width - page_offset_width_p                     

   
  , localparam fe_queue_width_lp=
  ($bits(bp_fe_queue_type_e)                                                                       
   + 
  (1 + (((
  (vaddr_width_p + instr_width_p + branch_metadata_fwd_width_p)
         
                )>(
  (vaddr_width_p + $bits(bp_fe_exception_code_e))
                                
                )) ? (
  (vaddr_width_p + instr_width_p + branch_metadata_fwd_width_p)
         
                ) : (
  (vaddr_width_p + $bits(bp_fe_exception_code_e))
                                
                ))
                                                                                  
   )
                        
   )
 
  , localparam fe_cmd_width_lp=
  (vaddr_width_p                                                                                  
   + $bits(bp_fe_command_queue_opcodes_e)                                                          
   + 
  (1+(((
  ($bits(bp_fe_command_queue_subopcodes_e)                                                         
   + branch_metadata_fwd_width_p + $bits(bp_fe_misprediction_reason_e) + 3)
       
              )>((((
  (1+branch_metadata_fwd_width_p)
          
                        )>((((
  (
  (paddr_width_p - bp_page_offset_width_gp + 6)
)
             
                                  )>(
  (asid_width_p + 2)
           
                                  )) ? (
  (
  (paddr_width_p - bp_page_offset_width_gp + 6)
)
             
                                  ) : (
  (asid_width_p + 2)
           
                                  ))
                                                                
                        )) ? (
  (1+branch_metadata_fwd_width_p)
          
                        ) : ((((
  (
  (paddr_width_p - bp_page_offset_width_gp + 6)
)
             
                                  )>(
  (asid_width_p + 2)
           
                                  )) ? (
  (
  (paddr_width_p - bp_page_offset_width_gp + 6)
)
             
                                  ) : (
  (asid_width_p + 2)
           
                                  ))
                                                                
                        ))
                                                                          
              )) ? (
  ($bits(bp_fe_command_queue_subopcodes_e)                                                         
   + branch_metadata_fwd_width_p + $bits(bp_fe_misprediction_reason_e) + 3)
       
              ) : ((((
  (1+branch_metadata_fwd_width_p)
          
                        )>((((
  (
  (paddr_width_p - bp_page_offset_width_gp + 6)
)
             
                                  )>(
  (asid_width_p + 2)
           
                                  )) ? (
  (
  (paddr_width_p - bp_page_offset_width_gp + 6)
)
             
                                  ) : (
  (asid_width_p + 2)
           
                                  ))
                                                                
                        )) ? (
  (1+branch_metadata_fwd_width_p)
          
                        ) : ((((
  (
  (paddr_width_p - bp_page_offset_width_gp + 6)
)
             
                                  )>(
  (asid_width_p + 2)
           
                                  )) ? (
  (
  (paddr_width_p - bp_page_offset_width_gp + 6)
)
             
                                  ) : (
  (asid_width_p + 2)
           
                                  ))
                                                                
                        ))
                                                                          
              ))
                                                                                    
   )
      
   )


   
  
  , localparam cce_mem_payload_width_lp = 
  (3+lce_id_width_p+( ((lce_assoc_p)==1) ? 1 : $clog2((lce_assoc_p)))+$bits(bp_coh_states_e))

                                      
  
  , localparam cce_mem_msg_header_width_lp = 
  ($bits(bp_bedrock_msg_u)+paddr_width_p+$bits(bp_bedrock_msg_size_e)+cce_mem_payload_width_lp)

  
  
  , localparam cce_mem_msg_width_lp = 
  (
  ($bits(bp_bedrock_msg_u)+paddr_width_p+$bits(bp_bedrock_msg_size_e)+cce_mem_payload_width_lp)
+cce_block_width_p)




   // TRACE enable parameters
   , parameter icache_trace_p              = 0
   , parameter dcache_trace_p              = 0
   , parameter lce_trace_p                 = 0
   , parameter cce_trace_p                 = 0
   , parameter dram_trace_p                = 0
   , parameter vm_trace_p                  = 0
   , parameter cmt_trace_p                 = 0
   , parameter core_profile_p              = 0
   , parameter pc_profile_p                = 0
   , parameter br_profile_p                = 0
   , parameter cosim_p                     = 0

   // COSIM parameters
   , parameter checkpoint_p                = 0
   , parameter cosim_memsize_p             = 0
   , parameter cosim_cfg_file_p            = "prog.cfg"
   , parameter cosim_instr_p               = 0
   , parameter warmup_instr_p              = 0

   // DRAM parameters
   , parameter preload_mem_p               = 0
   , parameter use_ddr_p                   = 0
   , parameter use_dramsim3_p              = 0
   , parameter dram_fixed_latency_p        = 0
   , parameter [paddr_width_p-1:0] mem_offset_p = dram_base_addr_gp
   , parameter mem_cap_in_bytes_p = 2**27
   , parameter mem_file_p         = "prog.mem"
   )
  (input clk_i
   , input reset_i
   , input dram_clk_i
   , input dram_reset_i
   );

 if (1)
    begin
      bind bp_cce_wrapper
        bp_me_nonsynth_cce_tracer
         #(.bp_params_p(bp_params_p))
         cce_tracer
          (.clk_i(clk_i & testbench.cce_trace_en_lo)
          ,.reset_i(reset_i)
          ,.freeze_i(cfg_bus_cast_i.freeze)

          ,.cce_id_i(cfg_bus_cast_i.cce_id)

          // To CCE
          ,.lce_req_i(lce_req_i)
          ,.lce_req_v_i(lce_req_v_i)
          ,.lce_req_yumi_i(lce_req_yumi_o)
          ,.lce_resp_i(lce_resp_i)
          ,.lce_resp_v_i(lce_resp_v_i)
          ,.lce_resp_yumi_i(lce_resp_yumi_o)

          // From CCE
          ,.lce_cmd_i(lce_cmd_o)
          ,.lce_cmd_v_i(lce_cmd_v_o)
          ,.lce_cmd_ready_i(lce_cmd_ready_i)

          // To CCE
          ,.mem_resp_i(mem_resp_i)
          ,.mem_resp_v_i(mem_resp_v_i)
          ,.mem_resp_yumi_i(mem_resp_yumi_o)

          // From CCE
          ,.mem_cmd_i(mem_cmd_o)
          ,.mem_cmd_v_i(mem_cmd_v_o)
          ,.mem_cmd_ready_i(mem_cmd_ready_i)
          );

      bind bp_lce
        bp_me_nonsynth_lce_tracer
          #(.bp_params_p(bp_params_p)
            ,.sets_p(sets_p)
            ,.assoc_p(assoc_p)
            ,.block_width_p(block_width_p)
            )
          lce_tracer
          (.clk_i(clk_i & testbench.lce_trace_en_lo)
          ,.reset_i(reset_i)
          ,.lce_id_i(lce_id_i)
          ,.lce_req_i(lce_req_o)
          ,.lce_req_v_i(lce_req_v_o)
          ,.lce_req_ready_i(lce_req_ready_i)
          ,.lce_resp_i(lce_resp_o)
          ,.lce_resp_v_i(lce_resp_v_o)
          ,.lce_resp_ready_i(lce_resp_ready_i)
          ,.lce_cmd_i(lce_cmd_i)
          ,.lce_cmd_v_i(lce_cmd_v_i)
          ,.lce_cmd_yumi_i(lce_cmd_yumi_o)
          ,.lce_cmd_o_i(lce_cmd_o)
          ,.lce_cmd_o_v_i(lce_cmd_v_o)
          ,.lce_cmd_o_ready_i(lce_cmd_ready_i)
          );
    end


   
endmodule   
