// See LICENSE for license details.

#include <stdint.h>
#include <string.h>
#include <stdio.h>

#include "riscv_test.h"

#define NC 16

#define MMIO_BASE_ADDR   0x0100000
#define MMIO_GETCHAR_ADDR 0x0100000
#define MMIO_PUTCHAR_ADDR 0x0101000
#define MMIO_FINISH_ADDR 0x0102000
#define CLINT_BASE_ADDR  0x0300000

#if __riscv_xlen == 32
# define SATP_MODE_CHOICE SATP_MODE_SV32
#elif defined(Sv48)
# define SATP_MODE_CHOICE SATP_MODE_SV48
#else
# define SATP_MODE_CHOICE SATP_MODE_SV39
#endif

void trap_entry();
void pop_tf(trapframe_t*);

volatile uint64_t tohost;
volatile uint64_t fromhost;

static void do_tohost(uint64_t tohost_value)
{
  while (tohost)
    fromhost = 0;
  tohost = tohost_value;
}

volatile uint64_t start_barrier = 0;
volatile uint64_t exclusion = 0;

void lock() {
  asm volatile ("1:\n\t"
                "sd t0, -8(sp)\n\t"
                "sd t1, -16(sp)\n\t"
                "li t0, 1\n\t"
                "lr.d t1, (%0)\n\t"
                "bnez t1, 1b\n\t"
                "sc.d t1, t0, (%0)\n\t"
                "bnez t1, 1b\n\t"
                "ld t0, -8(sp)\n\t"
                "ld t1, -16(sp)\n\t"
                : : "r" (&exclusion) :);
}

void unlock() {
  __sync_synchronize(); // Memory barrier.
  exclusion = 0;
}

#define pa2kva(pa) ((void*)(pa) - DRAM_BASE - MEGAPAGE_SIZE)
#define uva2kva(pa) ((void*)(pa) - MEGAPAGE_SIZE)

#define vpn0(va) ((va >> PGSHIFT) % (1 << PTIDXBITS))
#define vpn1(va) ((va >> (PGSHIFT + PTIDXBITS)) % (1 << PTIDXBITS))
#define vpn2(va) ((va >> (PGSHIFT + 2*PTIDXBITS)) % (1 << PTIDXBITS))

#define flush_page(addr) asm volatile ("sfence.vma %0" : : "r" (addr) : "memory")

static uint64_t lfsr63(uint64_t x)
{
  uint64_t bit = (x ^ (x >> 1)) & 1;
  return (x >> 1) | (bit << 62);
}

static void cputchar(int x)
{
  char ch = (char)x;
  uint64_t mhartid = read_csr(mhartid);
  char* ch_ptr = (char*)(0x0101000 + (mhartid << 3));
  *ch_ptr = ch;
}

static void cputstring(const char* s)
{
  while (*s)
    cputchar(*s++);
}

static void terminate(int code)
{
  uint64_t mhartid = read_csr(mhartid);
  uint64_t *finish_address = (uint64_t*)(MMIO_FINISH_ADDR + (mhartid << 3));
  *finish_address = code;
  while (1);
}

void wtf()
{
  terminate(841);
}

#define stringify1(x) #x
#define stringify(x) stringify1(x)
#define assert(x) do { \
  if (x) break; \
  cputstring("Assertion failed: " stringify(x) "\n"); \
  terminate(3); \
} while(0)

#if SATP_MODE_CHOICE == SATP_MODE_SV39
# define NPT 6
# define l1pt pt[hartid][0]
# define user_l2pt pt[hartid][1]
# define kernel_l2pt pt[hartid][2]
# define user_l3pt pt[hartid][3]
# define mmio_l3pt pt[hartid][4]
# define clint_l3pt pt[hartid][5]
#else
# error Unknown SATP_MODE_CHOICE
#endif

pte_t pt[NC][NPT][PTES_PER_PT] __attribute__((aligned(PGSIZE)));

typedef struct { pte_t addr; void* next; } freelist_t;

freelist_t freelist_nodes[MAX_TEST_PAGES];
freelist_t *freelist_head, *freelist_tail;

void handle_fault(uintptr_t addr, uintptr_t cause, uintptr_t hartid)
{
  assert(addr >= PGSIZE && addr < MAX_TEST_PAGES * PGSIZE);
  addr = addr/PGSIZE*PGSIZE;

  if (user_l3pt[addr/PGSIZE]) {
    if (!(user_l3pt[addr/PGSIZE] & PTE_A)) {
      user_l3pt[addr/PGSIZE] |= PTE_A;
    } else {
      assert(!(user_l3pt[addr/PGSIZE] & PTE_D) && cause == CAUSE_STORE_PAGE_FAULT);
      user_l3pt[addr/PGSIZE] |= PTE_D;
    }
    flush_page(addr);
    return;
  }

  lock();
  
  freelist_t* node = freelist_head;
  assert(node);
  freelist_head = node->next;
  if (freelist_head == freelist_tail)
    freelist_tail = 0;
  
  unlock();

  uintptr_t new_pte = (node->addr >> PGSHIFT << PTE_PPN_SHIFT) | PTE_V | PTE_U | PTE_R | PTE_W | PTE_X;
  user_l3pt[addr/PGSIZE] = new_pte | PTE_A | PTE_D;
  flush_page(addr);

  uintptr_t sstatus = set_csr(sstatus, SSTATUS_SUM);
  memcpy((void*)addr, uva2kva(addr), PGSIZE);
  write_csr(sstatus, sstatus);

  user_l3pt[addr/PGSIZE] = new_pte;
  flush_page(addr);

  __builtin___clear_cache(0,0);
}

void handle_trap(trapframe_t* tf)
{
  if (tf->cause == CAUSE_FETCH_PAGE_FAULT || tf->cause == CAUSE_LOAD_PAGE_FAULT || tf->cause == CAUSE_STORE_PAGE_FAULT) {
    handle_fault(tf->badvaddr, tf->cause, tf->hartid);
  }
  else
    assert(!"unexpected exception");

  pop_tf(tf);
}

static void coherence_torture()
{
  // cause coherence misses without affecting program semantics
  uint64_t random = 0;
  while (1) {
    uintptr_t paddr = DRAM_BASE + ((random % (2 * (MAX_TEST_PAGES + 1) * PGSIZE)) & -4);
#ifdef __riscv_atomic
    if (random & 1) // perform a no-op write
      asm volatile ("amoadd.w zero, zero, (%0)" :: "r"(paddr));
    else // perform a read
#endif
      asm volatile ("lw zero, (%0)" :: "r"(paddr));
    random = lfsr63(random);
  }
}

void vm_boot(uintptr_t test_addr)
{
  uint64_t random = ENTROPY;
  uint64_t hartid = read_csr(mhartid);
  if (hartid > 0)
    coherence_torture();

  _Static_assert(SIZEOF_TRAPFRAME_T == sizeof(trapframe_t), "???");
      
#if (MAX_TEST_PAGES > PTES_PER_PT) || (DRAM_BASE % MEGAPAGE_SIZE) != 0
# error
#endif
    // map user to lowermost megapage
    l1pt[0] = ((pte_t)user_l2pt >> PGSHIFT << PTE_PPN_SHIFT) | PTE_V;
    // map kernel to uppermost megapage
#if SATP_MODE_CHOICE == SATP_MODE_SV39
    l1pt[PTES_PER_PT-1] = ((pte_t)kernel_l2pt >> PGSHIFT << PTE_PPN_SHIFT) | PTE_V;
    
    kernel_l2pt[PTES_PER_PT-1] = (DRAM_BASE/RISCV_PGSIZE << PTE_PPN_SHIFT) | PTE_V | PTE_R | PTE_W | PTE_X | PTE_A | PTE_D;
    
    user_l2pt[0] = ((pte_t)user_l3pt >> PGSHIFT << PTE_PPN_SHIFT) | PTE_V;
    //user_l2pt[vpn1(MMIO_BASE_ADDR)] = ((pte_t)mmio_l3pt >> PGSHIFT << PTE_PPN_SHIFT) | PTE_V;
    //user_l2pt[vpn1(CLINT_BASE_ADDR)] = ((pte_t)clint_l3pt >> PGSHIFT << PTE_PPN_SHIFT) | PTE_V;
    
    //mmio_l3pt[vpn0(MMIO_GETCHAR_ADDR)] = (MMIO_GETCHAR_ADDR >> PGSHIFT << PTE_PPN_SHIFT) | PTE_V | PTE_R | PTE_W | PTE_X | PTE_A | PTE_D;
    //mmio_l3pt[vpn0(MMIO_PUTCHAR_ADDR)] = (MMIO_PUTCHAR_ADDR >> PGSHIFT << PTE_PPN_SHIFT) | PTE_V | PTE_R | PTE_W | PTE_X | PTE_A | PTE_D;
    //mmio_l3pt[vpn0(MMIO_FINISH_ADDR)] = (MMIO_FINISH_ADDR >> PGSHIFT << PTE_PPN_SHIFT) | PTE_V | PTE_R | PTE_W | PTE_X | PTE_A | PTE_D;
    //clint_l3pt[vpn0(CLINT_BASE_ADDR)] = (CLINT_BASE_ADDR >> PGSHIFT << PTE_PPN_SHIFT) | PTE_V | PTE_R | PTE_W | PTE_X | PTE_A | PTE_D;
#else
# error
#endif

  uintptr_t vm_choice = SATP_MODE_CHOICE;
  uintptr_t sptbr_value = ((uintptr_t)l1pt >> PGSHIFT)
                        | (vm_choice * (SATP_MODE & ~(SATP_MODE<<1)));
  write_csr(sptbr, sptbr_value);
  if (read_csr(sptbr) != sptbr_value)
    assert(!"unsupported satp mode");

  // Set up PMPs if present, ignoring illegal instruction trap if not.
  uintptr_t pmpc = PMP_NAPOT | PMP_R | PMP_W | PMP_X;
  uintptr_t pmpa = ((uintptr_t)1 << (__riscv_xlen == 32 ? 31 : 53)) - 1;
  asm volatile ("la t0, 1f\n\t"
                "csrrw t0, mtvec, t0\n\t"
                "csrw pmpaddr0, %1\n\t"
                "csrw pmpcfg0, %0\n\t"
                ".align 2\n\t"
                "1:"
                "csrrw t0, mtvec, t0\n\t"
                : : "r" (pmpc), "r" (pmpa) : "t0");

  // set up supervisor trap handling
  write_csr(stvec, pa2kva(trap_entry));
  write_csr(sscratch, pa2kva(read_csr(mscratch)));
  write_csr(medeleg,
    (1 << CAUSE_FETCH_PAGE_FAULT) |
    (1 << CAUSE_LOAD_PAGE_FAULT) |
    (1 << CAUSE_STORE_PAGE_FAULT));

  if(hartid == 0) {

    random = 1 + (random % MAX_TEST_PAGES);
    freelist_head = pa2kva((void*)&freelist_nodes[0]);
    freelist_tail = pa2kva(&freelist_nodes[MAX_TEST_PAGES-1]);
    for (long i = 0; i < MAX_TEST_PAGES; i++)
    {
      freelist_nodes[i].addr = DRAM_BASE + MEGAPAGE_SIZE + random*PGSIZE;
      freelist_nodes[i].next = pa2kva(&freelist_nodes[i+1]);
      random = LFSR_NEXT(random);
    }
    freelist_nodes[MAX_TEST_PAGES-1].next = 0;
    start_barrier = 1;
  }
  else {
    while(start_barrier != 1) {}
  }

  trapframe_t tf;
  memset(&tf, 0, sizeof(tf));
  tf.epc = test_addr - DRAM_BASE;
  tf.hartid = hartid;
  pop_tf(&tf);
}
