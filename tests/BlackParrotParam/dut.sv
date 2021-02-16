
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


module bp_be_ptw
  import bp_common_pkg::*;
  import bp_common_rv64_pkg::*;
  import bp_common_aviary_pkg::*;
  import bp_be_pkg::*;
  import bp_be_dcache_pkg::*;
  #(parameter bp_cfg_e cfg_p = e_bp_inv_cfg
    
  , localparam bp_proc_param_s proc_param_lp = all_cfgs_gp[cfg_p]                            
                                                                                                   
  , localparam num_core_p = proc_param_lp.num_core                                                 
  , localparam num_cce_p  = proc_param_lp.num_cce                                                  
  , localparam num_lce_p  = proc_param_lp.num_lce                                                  
                                                                                                   
  , localparam vaddr_width_p = proc_param_lp.vaddr_width                                           
  , localparam paddr_width_p = proc_param_lp.paddr_width                                           
  , localparam asid_width_p  = proc_param_lp.asid_width                                            
                                                                                                   
  , localparam branch_metadata_fwd_width_p = proc_param_lp.branch_metadata_fwd_width               
  , localparam btb_tag_width_p             = proc_param_lp.btb_tag_width                           
  , localparam btb_idx_width_p             = proc_param_lp.btb_idx_width                           
  , localparam bht_idx_width_p             = proc_param_lp.bht_idx_width                           
  , localparam ras_idx_width_p             = proc_param_lp.ras_idx_width                           
                                                                                                   
  , localparam itlb_els_p              = proc_param_lp.itlb_els                                    
  , localparam dtlb_els_p              = proc_param_lp.dtlb_els                                    
                                                                                                   
  , localparam lce_sets_p              = proc_param_lp.lce_sets                                    
  , localparam lce_assoc_p             = proc_param_lp.lce_assoc                                   
  , localparam cce_block_width_p       = proc_param_lp.cce_block_width                             
  , localparam num_cce_instr_ram_els_p = proc_param_lp.num_cce_instr_ram_els                       
                                                                                                   
  , localparam fe_queue_fifo_els_p = proc_param_lp.fe_queue_fifo_els                               
  , localparam fe_cmd_fifo_els_p   = proc_param_lp.fe_cmd_fifo_els                                 
                                                                                                   
  , localparam async_coh_clk_p        = proc_param_lp.async_coh_clk                                
  , localparam coh_noc_flit_width_p   = proc_param_lp.coh_noc_flit_width                           
  , localparam coh_noc_cid_width_p    = proc_param_lp.coh_noc_cid_width                            
  , localparam coh_noc_len_width_p    = proc_param_lp.coh_noc_len_width                            
  , localparam coh_noc_y_cord_width_p = proc_param_lp.coh_noc_y_cord_width                         
  , localparam coh_noc_x_cord_width_p = proc_param_lp.coh_noc_x_cord_width                         
  , localparam coh_noc_y_dim_p        = proc_param_lp.coh_noc_y_dim                                
  , localparam coh_noc_x_dim_p        = proc_param_lp.coh_noc_x_dim                                
  , localparam coh_noc_cord_width_p   = coh_noc_x_cord_width_p + coh_noc_y_cord_width_p            
  , localparam coh_noc_dims_p         = 2                                                          
  , localparam coh_noc_dirs_p         = coh_noc_dims_p*2 + 1                                       
  , localparam int coh_noc_cord_markers_pos_p[coh_noc_dims_p:0] =                                  
      '{coh_noc_cord_width_p, coh_noc_x_cord_width_p, 0}                                           
                                                                                                   
  , localparam cfg_core_width_p = proc_param_lp.cfg_core_width                                     
  , localparam cfg_addr_width_p = proc_param_lp.cfg_addr_width                                     
  , localparam cfg_data_width_p = proc_param_lp.cfg_data_width                                     
                                                                                                   
  , localparam async_mem_clk_p           = proc_param_lp.async_mem_clk                             
  , localparam mem_noc_max_credits_p     = proc_param_lp.mem_noc_max_credits                       
  , localparam mem_noc_flit_width_p      = proc_param_lp.mem_noc_flit_width                        
  , localparam mem_noc_reserved_width_p  = proc_param_lp.mem_noc_reserved_width                    
  , localparam mem_noc_cid_width_p       = proc_param_lp.mem_noc_cid_width                         
  , localparam mem_noc_len_width_p       = proc_param_lp.mem_noc_len_width                         
  , localparam mem_noc_y_cord_width_p    = proc_param_lp.mem_noc_y_cord_width                      
  , localparam mem_noc_x_cord_width_p    = proc_param_lp.mem_noc_x_cord_width                      
  , localparam mem_noc_y_dim_p           = proc_param_lp.mem_noc_y_dim                             
  , localparam mem_noc_x_dim_p           = proc_param_lp.mem_noc_x_dim                             
  , localparam mem_noc_cord_width_p      = mem_noc_x_cord_width_p + mem_noc_y_cord_width_p         
  , localparam mem_noc_dims_p            = 2                                                       
  , localparam mem_noc_dirs_p            = mem_noc_dims_p*2 + 1                                    
  , localparam int mem_noc_cord_markers_pos_p[mem_noc_dims_p:0] =                                  
      '{mem_noc_cord_width_p, mem_noc_x_cord_width_p, 0}                                           
                                                                                                   
  , localparam num_mem_p    = mem_noc_x_dim_p + 2                                                  
  , localparam mmio_x_pos_p = (mem_noc_x_dim_p+1)/2                                                
                                                                                                   
  , localparam dword_width_p       = 64                                                            
  , localparam instr_width_p       = 32                                                            
  , localparam reg_addr_width_p    = 5                                                             
  , localparam page_offset_width_p = 12                                                            
                                                                                                   
  , localparam vtag_width_p  = proc_param_lp.vaddr_width - page_offset_width_p                     
  , localparam ptag_width_p  = proc_param_lp.paddr_width - page_offset_width_p                     

    
  , localparam fe_queue_width_lp=
  ($bits(bp_fe_queue_type_e)                                                                       
   + 
  (1 + (((
  (vaddr_width_p + bp_instr_width_gp + branch_metadata_fwd_width_p)
         
                )>(
  (vaddr_width_p + $bits(bp_fe_exception_code_e))
                                
                )) ? (
  (vaddr_width_p + bp_instr_width_gp + branch_metadata_fwd_width_p)
         
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
   + branch_metadata_fwd_width_p                    
                                                 + $bits(bp_fe_misprediction_reason_e) + 1)
       
              )>((((
  (branch_metadata_fwd_width_p                    
                                                )
          
                        )>((((
  (
  (paddr_width_p                                  
                                                 - bp_page_offset_width_gp + 6)
)
             
                                  )>(
  (asid_width_p                                   
                                                 + 2)
           
                                  )) ? (
  (
  (paddr_width_p                                  
                                                 - bp_page_offset_width_gp + 6)
)
             
                                  ) : (
  (asid_width_p                                   
                                                 + 2)
           
                                  ))
                                                                
                        )) ? (
  (branch_metadata_fwd_width_p                    
                                                )
          
                        ) : ((((
  (
  (paddr_width_p                                  
                                                 - bp_page_offset_width_gp + 6)
)
             
                                  )>(
  (asid_width_p                                   
                                                 + 2)
           
                                  )) ? (
  (
  (paddr_width_p                                  
                                                 - bp_page_offset_width_gp + 6)
)
             
                                  ) : (
  (asid_width_p                                   
                                                 + 2)
           
                                  ))
                                                                
                        ))
                                                                          
              )) ? (
  ($bits(bp_fe_command_queue_subopcodes_e)                                                         
   + branch_metadata_fwd_width_p                    
                                                 + $bits(bp_fe_misprediction_reason_e) + 1)
       
              ) : ((((
  (branch_metadata_fwd_width_p                    
                                                )
          
                        )>((((
  (
  (paddr_width_p                                  
                                                 - bp_page_offset_width_gp + 6)
)
             
                                  )>(
  (asid_width_p                                   
                                                 + 2)
           
                                  )) ? (
  (
  (paddr_width_p                                  
                                                 - bp_page_offset_width_gp + 6)
)
             
                                  ) : (
  (asid_width_p                                   
                                                 + 2)
           
                                  ))
                                                                
                        )) ? (
  (branch_metadata_fwd_width_p                    
                                                )
          
                        ) : ((((
  (
  (paddr_width_p                                  
                                                 - bp_page_offset_width_gp + 6)
)
             
                                  )>(
  (asid_width_p                                   
                                                 + 2)
           
                                  )) ? (
  (
  (paddr_width_p                                  
                                                 - bp_page_offset_width_gp + 6)
)
             
                                  ) : (
  (asid_width_p                                   
                                                 + 2)
           
                                  ))
                                                                
                        ))
                                                                          
              ))
                                                                                    
   )
      
   )



    ,parameter pte_width_p              = bp_sv39_pte_width_gp
    ,parameter page_table_depth_p       = bp_sv39_page_table_depth_gp
    
    ,localparam vpn_width_lp            = vaddr_width_p - page_offset_width_p
    ,localparam ppn_width_lp            = paddr_width_p - page_offset_width_p
    ,localparam dcache_pkt_width_lp     = 
  ($bits(bp_be_dcache_opcode_e)+page_offset_width_p+pte_width_p)
    
    ,localparam tlb_entry_width_lp      = 
  (paddr_width_p - bp_page_offset_width_gp + 6)

    ,localparam lg_page_table_depth_lp  = ( ((page_table_depth_p)==1) ? 1 : $clog2((page_table_depth_p)))

    ,localparam pte_size_in_bytes_lp    = pte_width_p/rv64_byte_width_gp
    ,localparam lg_pte_size_in_bytes_lp = ( ((pte_size_in_bytes_lp)==1) ? 1 : $clog2((pte_size_in_bytes_lp)))
    ,localparam partial_vpn_width_lp    = page_offset_width_p - lg_pte_size_in_bytes_lp
  )
  (
  );
  
  
  assign tlb_w_entry.ptag       = translation_en_i ? writeback_ppn : ppn_width_lp'(vpn_r);

 
endmodule
