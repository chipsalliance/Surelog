

/*
 * This test checks that JALR with funct3 != 0 is an illegal instruction
 */
#include <stdint.h>
#include "bp_utils.h"

void trap_success() {
    // Read mcause
    uint64_t mcause;
    __asm__ __volatile__ ("csrr %0, mcause" : "=r" (mcause));

    // Check for illegal instruction
    if (mcause == 2)
      bp_finish(0);
    else
      bp_finish(1);
}

void main(uint64_t argc, char * argv[]) {
   // Set up trap to alternate handler
   __asm__ __volatile__ ("csrw mtvec, %0": : "r" (&trap_success));
   // Illegal JALR with funct3 != 0
   __asm__ __volatile__ (".word 0xfdc9a1e7");

   bp_finish(1);
}

