
/*
 * This test checks that SATP updates are reflected in instruction fetches
 *   WITHOUT an sfence
 */
#include <stdint.h>
#include "bp_utils.h"

uint64_t null_pte = 0;

void trap_success() {
    // Read mcause
    uint64_t mcause;
    __asm__ __volatile__ ("csrr %0, mcause" : "=r" (mcause));

    // Check for instruction page fault
    if (mcause == 12)
      bp_finish(0);
    else
      bp_finish(1);
}

void set_satp() {
  // Set satp to translation enable with a null address
  uint64_t translation_en = 0x8000000000000000;
  uint64_t pte_entry = (uint64_t) &null_pte;
  uint64_t new_satp  = translation_en | (pte_entry >> 12);
  __asm__ __volatile__ ("csrw satp, %0": : "r" (new_satp));

  // Now that we've set satp, we should page fault and not reach here
  bp_finish(1);
}

void main(uint64_t argc, char * argv[]) {
   // Set up trap to alternate handler
   __asm__ __volatile__ ("csrw mtvec, %0": : "r" (&trap_success));
   // Set up mepc
   __asm__ __volatile__ ("csrw mepc, %0": : "r" (&set_satp));
   // Set mpp == s-mode
   uint64_t mpp_equals_s = 0x800;
   __asm__ __volatile__ ("csrw mstatus, %0" : : "r" (mpp_equals_s));
   // Trap to set_satp, and S-mode translation disabled
   __asm__ __volatile__ ("mret");

   bp_finish(1);
}

