#ifndef INIT_H
#define INIT_H

#define MTIME           (*(volatile long long *)(0x00300000 + 0x8000))
#define MTIMECMP        ((volatile long long *)(0x00300000 + 0x4000))

#define csr_read(csr)                                   \
({                                                      \
    register unsigned long __v;                         \
    __asm__ __volatile__ ("csrr %0, " #csr              \
                  : "=r" (__v));                        \
    __v;                                                \
})

typedef void* (*trap_handler_t)(unsigned hartid, unsigned mcause, void *mepc,
        void *sp);
void set_trap_handler(trap_handler_t handler);
void enable_timer_interrupts();

#endif
