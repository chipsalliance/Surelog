

/*
 * This test checks if timer interrupts are working 
 */
#include <stdint.h>
#include "bp_utils.h"
#define NUM_INTERRUPTS 8

uint8_t int_count = 48;
uint64_t *mtimecmp = 0x304000;
uint64_t *mtime = 0x30bff8;

void pass() { bp_finish(0); }
void fail() { bp_finish(1); }

void trap_success(void) __attribute__((interrupt));
void trap_success() {
    // Read mcause
    uint64_t mcause;
    __asm__ __volatile__ ("csrr %0, mcause" : "=r" (mcause));

    // Check for interrupt
    if ((mcause >> 63) == 1) {
      if(((mcause & 7) == 4) || ((mcause & 7) == 5) || ((mcause & 7) == 7))
        int_count++;
        // Sufficiently far in the future to have delayed interrupts
        // Writes to mtimecmp clears the interrupt
        *mtimecmp = *mtime + 1024;
        bp_cprint(int_count);
        bp_cprint(10);
        if((int_count - 48) == NUM_INTERRUPTS)
          pass();
    }
    else {
      bp_cprint(int_count);
      bp_cprint(10);
      fail();
    }
}

void main(uint64_t argc, char * argv[]) {
   uint64_t mie = (1 << 7) | (1 << 5) | (1 << 4); // M + S + U timer interrupt enable
   uint64_t mstatus = (1 << 3) | (1 << 1) | (1 << 0); // Global interrupt enable
   // Set up trap to alternate handler
   __asm__ __volatile__ ("csrw mtvec, %0": : "r" (&trap_success));
   // Setting up mtimecmp and mtime with some arbitrary values
   *mtimecmp = 64;
   *mtime = 0;
   // Enabling interrupts for User, Supervisor and Machine mode
   __asm__ __volatile__ ("csrw mie, %0": : "r" (mie));
   __asm__ __volatile__ ("csrw mstatus, %0" : : "r" (mstatus));
  
   while(1);
}

